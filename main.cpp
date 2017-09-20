/* Code written by Kliment Serafimov */

#include <fstream>
#include <iomanip>
#include <iostream>

#include <map>
#include <set>
#include <cmath>
#include <queue>
#include <stack>
#include <math.h>
#include <time.h>
#include <string>
#include <vector>
#include <cstring>
#include <cstdlib>
#include <cassert>
#include <algorithm>

#define P push
#define f first
#define s second
#define pb push_back
#define mp make_pair
#define DEC 0.00000001
#define MAX 2139062143
#define inf MAX/2
#define MAX_63  1061109567
#define MAXll 9187201950435737471
#define bp(a) __builtin_popcount(a)
#define rand(a, b) ((rand()%(b-a+1))+a)
#define MEM(a, b) memset(a, b, sizeof(a))
#define sort_v(a) sort(a.begin(), a.end())
#define rev_v(a)  reverse(a.begin(), a.end())

//#define fin cin
//#define fout cout
using namespace std;
//ifstream fin(".in");
//ofstream fout(".out");

#define maxB 8
///NODE of A-B Tree

#define print_queries 0
#define AUTO_TEST 1
#define max_n 1000
#define max_time 1000*max_n

string int_to_string(int n)
{
    if(n == 0)
    {
        return "0";
    }
    string ret;
    while(n>0)
    {
        ret+=(n%10)+'0';
        n/=10;
    }
    rev_v(ret);
    return ret;
}

class element
{
public:
    bool is_constant;
        int constant;
    ///if not contant
        int sum;
        int product;
    void init()
    {
        sum = 0;
        product = 1;
        is_constant = false;
    }
    element()
    {
        init();
    }
    bool is_sum(int type)
    {
        return (type == 0);
    }
    bool is_product(int type)
    {
        return (type == 1);
    }
    bool is_set(int type)
    {
        return (type == 2);
    }
    element(int type, int val)
    {
        init();
        if(is_sum(type))
        {
            sum = val;
        }
        else if(is_product(type))
        {
            product = val;
        }
        else
        {
            assert(is_set(type));
            is_constant = true;
            constant = val;
        }
    }
    void merge(element *right_operand)
    {
        element* left_operand = this;
        if(is_constant || right_operand->is_constant)
        {
            if(right_operand->is_constant)
            {
                is_constant = true;
                constant = right_operand->constant;
            }
            else
            {
                assert(is_constant);
                constant*=(right_operand->product);
                constant+=(right_operand->sum);
            }
        }
        else
        {
            product*=right_operand->product;
            sum = sum*right_operand->product + right_operand->sum;
        }
    }
    int get()
    {
        if(is_constant)
        {
            return constant;
        }
        else
        {
            return product+sum;
        }
    }
    string print()
    {
        if(is_constant)
        {
            return int_to_string(constant);
        }
        else
        {
            return "*"+int_to_string(product)+"+"+int_to_string(sum);
        }
    }
    ~element()
    {
    }
};

class node
{
    public:
    int a, b;

    int num_children;
    node* child[maxB+1];
    int left_bound;
    int right_bound;

    element* operation;

    node(int _a, int _b, int moment, int _right_bound, element* operand)
    {
        a = _a;
        b = _b;
        left_bound = moment;
        right_bound = _right_bound;
        num_children = 0;
        operation = operand;
    }
    node(int _a, int _b)
    {
        a = _a;
        b = _b;
    }

    void update_bounds()
    {
        if(num_children>0)
        {
            left_bound = child[0]->left_bound;
            right_bound = child[num_children-1]->right_bound;
        }
    }
    void update_operand()
    {
        if(num_children>0)
        {
            operation = new element();
            for(int i = 0;i<num_children;i++)
            {
                if(i!=num_children-1)
                {
                    child[i]->right_bound = child[i+1]->left_bound;
                }
                operation->merge(child[i]->operation);
            }
            update_bounds();
        }
    }
    node* create_leaf(int moment, int type, int val)
    {
        if(moment>=left_bound)
        {
            assert(moment<right_bound);
            int old_rb = right_bound;
            right_bound = min(right_bound, moment);
            node* ret_node = new node(a, b, moment, old_rb, new element(type, val));
            return ret_node;
        }
        else
        {
            node *new_node = new node(a, b, left_bound, right_bound, operation);
            right_bound = left_bound;
            left_bound = moment;
            operation = new element(type, val);
            return new_node;
        }
    }
    void insert_node(int moment, int type, int val)
    {
        //assert(left_bound<=moment && moment<right_bound);
        node* new_node = NULL;
        bool do_break = false;
        for(int i = 0; i<num_children&&!do_break;i++)
        {
            bool is_smallest = (i == 0 && moment < left_bound);
            if(is_smallest || (child[i]->left_bound <=moment && moment < child[i]->right_bound))
            {
                new_node = child[i]->insert(moment, type, val);
                if(new_node != NULL)
                {
                    for(int j = num_children;j>i;j--)
                    {
                        child[j+1] = child[j];
                    }
                    int new_child_at = i+1;
                    child[new_child_at] = new_node;
                    num_children++;
                }
                do_break = true;
            }
        }
    }
    node* split_node()
    {
        node* ret_node = NULL;
        if(num_children == b+1)
        {
            ret_node = new node(a, b);
            int aug_num_c = (b+1)/2;
            ret_node->num_children = 0;
            num_children = num_children - aug_num_c;
            for(int i = b, at = aug_num_c-1; i>=num_children; i--, at--)
            {
                ret_node->child[at] = child[i];
                ret_node->num_children++;
            }
            assert(ret_node->num_children == aug_num_c);
            ret_node->update_operand();
        }
        update_operand();
        return ret_node;
    }
    node* insert(int moment, int type, int val)
    {
        if(num_children == 0)
        {
            return create_leaf(moment, type, val);
        }
        insert_node(moment, type, val);
        node* ret_node = split_node();
        return ret_node;
    }
    element *query(int moment)
    {
        if(moment<left_bound)
        {
            return new element();
        }
        if(num_children == 0)
        {
            return operation;
        }
        element* ret = new element();

        for(int i = 0; i<num_children; i++)
        {
            if(child[i]->left_bound<=moment && moment<child[i]->right_bound)
            {
                ret->merge(child[i]->query(moment));
                break;
            }
            else
            {
                ret->merge(child[i]->operation);
            }
        }
        return ret;
    }
    node* combine(node *right_node)
    {
        if(num_children == 0)
        {
            assert(right_node->num_children == 0);
            return NULL;
        }
        assert(right_node->left_bound == right_bound);
        for(int i = num_children, j = 0; j<right_node->num_children; j++, i++)
        {
            child[i] = right_node->child[j];
        }
        right_bound = right_node->right_bound;
        num_children = num_children+right_node->num_children;
        return split_node();
    }
    void update_right_bound(int new_right_bound)
    {
        if(right_bound!=new_right_bound)
        {
            if(num_children != 0)
            {
                child[num_children-1]->update_right_bound(new_right_bound);
            }
            right_bound = new_right_bound;
        }
    }
    bool delete_at(int moment)
    {
        assert(left_bound<=moment && moment<right_bound);
        if(num_children == 0)
        {
            return true;
        }
        for(int i = 0; i<num_children; i++)
        {
            if(child[i]->left_bound<=moment && moment<child[i]->right_bound)
            {
                if(child[i]->delete_at(moment))
                {
                    update_bounds();
                    if(i!=num_children-1)
                    {
                        int add = 1;
                        if(child[i]->num_children == 0)
                        {
                            add = 0;
                        }
                        else
                        {
                            child[i]->update_right_bound(child[i+1]->left_bound);
                        }
                        node* new_node = child[i]->combine(child[i+1]);
                        if(new_node == NULL)
                        {
                            for(int j = i+add;j<num_children-1;j++)
                            {
                                child[j] = child[j+1];
                            }
                            int new_at = i+add;
                            if(new_at !=0 && new_at!= num_children-1)
                            {
                                child[new_at-1]->update_right_bound(child[new_at]->left_bound);
                            }
                            num_children--;
                        }
                        else
                        {
                            child[i+1] = new_node;
                        }
                    }
                    else
                    {
                        child[i-1]->update_right_bound(child[i]->left_bound);
                        node* new_node = child[i-1]->combine(child[i]);
                        if(new_node == NULL)
                        {
                            child[i-1]->update_right_bound(child[i]->right_bound);
                            right_bound = child[i]->right_bound;
                            num_children--;
                        }
                        else
                        {
                            child[i] = new_node;
                        }
                    }
                }
                if(i!=0 && num_children != i)
                {
                    child[i-1]->update_right_bound(child[i]->left_bound);
                }
                break;
            }
        }
        update_operand();
        if(num_children<a)
        {
            return true;
        }
        else
        {
            return false;
        }
    }
    string print_rb()
    {
        if(right_bound == inf) return "inf";
        else return int_to_string(right_bound);
    }
    void print(int c, int d)
    {
        for(int i = 0;i<c;i++) cout << " ";
        cout << "operation: " << operation->print() <<" | t = [" << left_bound <<", "<< print_rb() << ") " ;

        if(num_children > 0)
        {
            for(int i = 0;i<c;i++) cout << " ";cout << "num_children = " << num_children << " :: ";
        }
        cout << endl;
        for(int i = 0;i<num_children; i++)
        {
            child[i]->print(c+d, d);
        }
    }
};

class a_b_tree
{
    public:
    node *root;
    int a, b;
    a_b_tree(int _a, int _b)
    {
        a = _a;
        b = _b;
        root = NULL;
    }
    element *query(int moment)
    {
        if(root == NULL)
        {
            return new element();
        }
        return root->query(moment);
    }
    void insert(int moment, int type, int val)
    {
        if(root == NULL)
        {
            //cout << "new root!" <<endl;
            root = new node(a, b, moment, inf, new element(type, val));
            root->update_bounds();
        }
        else
        {
            node* augment_node = root->insert(moment, type, val);
            if(augment_node != NULL)
            {
                //cout << "new root!" <<endl;
                node* prev_root = root;
                root = new node(a, b);
                root->child[0] = prev_root;
                root->child[1] = augment_node;
                root->num_children = 2;
                root->update_operand();
            }
        }
    }
    void delete_at(int moment)
    {
        if(root == NULL)
        {

        }
        else if(moment<root->left_bound)
        {

        }
        else
        {
            root->delete_at(moment);
            if(root->num_children == 1)
            {
                //cout << "old root!" <<endl;
                root = root->child[0];
            }
            else if(root->num_children == 0)
            {
                root = NULL;
            }
        }
    }
    void print()
    {
        if(root == NULL)
        {

        }
        else
        {
            root->print(0, 2);
            cout << endl;
        }
    }
};


vector<pair<pair<int, int>, int> >  in;
vector<int> out;

int work_a_b_tree()
{
    int c = 0;
    a_b_tree* tree = new a_b_tree(2, 3);
    int q;
    if(AUTO_TEST) q = in.size();
    else cin >> q;
    for(int i = 0;i<q; i++)
    {
        //cout <<i << " " << q <<endl
        int t, type, val;
        if(AUTO_TEST)
        {
            t = in[i].f.f, type = in[i].f.s, val = in[i].s;
        }
        else cin >> t >> type;
        ///type, description
        ///0, insert sum
        ///1, insert multiply
        ///2, insert set
        ///3, query
        ///4, delete operation
        if(type == 3)
        {
            if(print_queries)cout <<"query: "<< t <<" "<< type <<endl;
            val = -1;
            if(AUTO_TEST)out.pb(tree->query(t)->get());
            else cout <<"result at: " << t <<" :: "<< tree->query(t)->get() <<endl;
        }
        else if(type == 4)
        {
            if(print_queries)cout <<"query: "<< t <<" "<< type <<endl;
            val = -1;
            tree->delete_at(t);
        }
        else
        {
            if(!AUTO_TEST)cin >> val;
            if(print_queries)cout <<"query: "<< t <<" "<< type <<" "<< val <<endl;
            tree->insert(t, type, val);
        }
        //tree->print();
    }
    return 0;
}

vector<int> oracle;
bool time_line[max_time+1];
class test
{
public:
    test(int n)
    {
        in.clear();
        out.clear();
        oracle.clear();
        MEM(time_line, 0);
        for(int i = 0;i<n;i++)
        {
            int t = rand(0, max_time);
            while(time_line[t] == 1)
            {
                t+=rand(0, max_time);
                t%=max_time;
            }
            time_line[t] = 1;
            int type = rand(0, 4);
            int val = rand(1, 4);
            in.pb(mp(mp(t, type), val));
        }
        vector<pair<pair<int, int>, int> > partial;
        for(int i = 0;i<in.size();i++)
        {
            if(in[i].f.s == 3)
            {
                element *rez = new element();
                for(int j = 0;j<partial.size() && partial[j].f.f<=in[i].f.f;j++)
                {
                    rez->merge(new element(partial[j].f.s, partial[j].s));
                }
                oracle.pb(rez->get());
            }
            else if(in[i].f.s == 4)
            {
                int j = 0;
                for(j = 0;j<(partial.size()) && partial[j].f.f<=in[i].f.f;)
                {
                    j++;
                }
                if(partial.size()>=1 && in[i].f.f >= partial[0].f.f)
                {
                    partial.erase(partial.begin()+j-1, partial.begin()+j);
                }
            }
            else
            {
                partial.pb(in[i]);
                sort_v(partial);
            }
        }
        //cout << "ORACLE COMPLETE" <<endl;
    }
    string check()
    {
        if(oracle.size() == out.size())
        {
            for(int i = 0;i<oracle.size();i++)
            {
                if(oracle[i] != out[i])
                {
                    cout << in.size()<<endl;
                    for(int j = 0;j<in.size();j++)
                    {
                        cout << in[j].f.f <<" "<< in[j].f.s<<" ";
                        if(in[j].f.s<=2)cout << in[j].s;
                        cout <<endl;
                    }
                    cout <<"missmatch here "<< oracle[i] <<" "<< out[i] <<endl;
                    return "NOT";
                }
            }
            return "OK";
        }
        else
        {
            cout << "num query missmatch" <<endl;
            return "NOT";
        }
    }
};

int main()
{
    int T = 100;
    int n = max_n;
    if(!AUTO_TEST) T = 1;
    int correct = 0;
    int total = 0;
    while(T--)
    {
        test *test_case;
        if(AUTO_TEST) test_case = new test(n);
        work_a_b_tree();
        if(AUTO_TEST)
        {
            string rez = test_case->check();
            correct+=(rez == "OK");
            total++;
            cout << rez <<endl;
        }
    }
    cout <<"correct: "<< correct <<"/"<<total <<endl;
    return 0;
}

