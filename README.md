# Brauer Groups of BG

## Guide to Repo
This repo currently contains some snippet code we wrote previously, as well as an implementation of ChatGPT of the algorithm proposed below.  We are currently working through it to check correctness.

## Algorithm 1:  Computing the covering
We want to present a covering for the partially ramified Brauer group.  That is, given a set of conjugacy classes $$\mathcal{C}=\{C_1,\dots,C_k\}$$ of a finite group $$G$$ we are computing the following fixed covering group of $$\text{Br}\_{\mathcal{C}}BG$$, which we will denote by  $$\widetilde{\text{Br}\_{\mathcal{C}}}BG$$.  This is the group of pairs $$(b_1,b_2)$$ where:
    * $$b_1$$ is an element of $$H^2(G, \mathbb{Z}/2\mathbb{Z})$$ whose associated extension class admits a marking, and
    * $$b_2$$ is an element of $$H^1(\mathbb{Q}(\zeta\_{2|G|}/\mathbb{Q}), \hat{G}[2])$$.
    * Writing $$\text{res}\_{C_i}$$ for the residue map at each $$C_i$$, we have $$\text{res}\_{C_i}(b_1)+\text{res}\_{C_i}(b_2)=0$$.  We compute each residue via separate algorithms on the factors.

### Step 0: Input
The input should be a group $$G$$ and a list $$C=\{C_1,\dots,C_k\}$$ of conjugacy classes in $$G$$.

### Step 0.5: Dump odd order groups
The Brauer group has even order, so if $$G$$ has odd order then there is no Brauer group.

### Step 1: Check validity of $$C$$
Check that $$\bigcup_i C_i$$ generates $$G$$.  Moreover, check that this union is closed under invertible powers (for example, by checking that for $$t$$ coprime to the size of $$G$$ we have $$C_i^t=C_j$$ for some $$j$$).  In doing this, store the group of integers $$k\in (\mathbb{Z}/2|G|)^\times[2^\infty]$$ such that $$C_i^{k}=C_i$$.  Call that group $$N_i$$.

### Step 2: Enumerate all geometric central extensions
Compute $$H^2(G,\mathbb{Z}/2\mathbb{Z})$$ as a group, and maintain the ability to map an element to a central extension.

### Step 3: Compute the subgroup of $$H^2(G,\mathbb{Z}/2\mathbb{Z})$$ which admit goemetric markings (so our geometric Brauer elements!)
#### 3.A: Reduce to those which have geometric markings
For each $$C_i$$, fixing a $$g_i\in C_i$$ there is a geometric residue map $$H^2(G,\mathbb{Z}/2\mathbb{Z})\to H^1(C_G(g_i), \mathbb{Z}/2\mathbb{Z})$$.  Compute each codomain as an $$\mathbb{F}_2$$-vector space, and then write the combined map
$$H^2(G,\mathbb{Z}/2\mathbb{Z})\to \prod_i H^2(C_G(g_i), \mathbb{Z}/2\mathbb{Z})$$ as a matrix and compute its kernel.

The map geometric residue is given as follows.  Given an element of $$H^2(G,\mathbb{Z}/2\mathbb{Z})$$, represented by an extension $$G_\beta$$ of $$G$$ by $$\mathbb{Z}/2\mathbb{Z}$$, the residue is represented by the cocycle which maps an element $$h\in C_G(g_i)$$ to the element $$z\in \mathbb{Z}/2\mathbb{Z}$$ such that for any two lifts $$\tilde{h},\tilde{g_i}$$ in $$G_\beta$$, we have $$\tilde{g_i}\tilde{h}=\tilde{h}\tilde{g_i}z$$.

End this stage with a basis for the kernel.

#### 3.B: Find markings
For each basis element from 3.A, we now want an explicit marking.  This is computed in a straightforward manner.  Let $$G_\beta$$ be the extension class associated to a basic element.  For each $$C_i$$, just take an element $$g_i\in C_i$$ and take a lift $$\tilde{g_i}\in G_\beta$$.  Then take its conjugacy class, call it $$D_i$$.  The marking is the data of the $$D_1,\dots,D_k$$.

### Step 4: Compute the "arithmetic residue" of the geometric Brauer elements
For each $$C_i$$, and each generator for step 3 do the following.  Choose a $$\tilde{g}_i\in D_i$$, and for each $$k\in N_i$$ store whether $$\tilde{g}_i^x$$ is conjugate to $$\tilde{g_i}$$.  Store this as the value of the residue at $$k$$.

### Step 5: Compute the residues of the algebraic Brauer group
The algebraic Brauer group elements are represented by elements of $$\text{Hom}(\mathbb{Z}/2|G|\mathbb{Z}, \hat{G}[2])$$.  The residue of an element $$b$$ of this group, evaluated at an element $$k\in N_i$$, is $$b(k)(C_i)$$. Here $$b(k)$$ has a well defined output on $$C_i$$ since it factors through the abelianisation.  Store the values as in step 4.


### Step 6: Match up pairs
Compare residues and assemble the appropriate pairs.

## Algorithm 2: Compute the Brauer group
Using the data computed in the previous group, we now compute the kernel of the covering.  This is determined mathematically as follows.  Let 
    * $$V:=\text{Im}(2(\hat{G}[4])\subset H^1(\mathbb{Q}(\zeta_{2|G|})/\mathbb{Q}), \hat{G}[2])$$.
    * $$W:=\text{Im}(\hat{G}/2\hat{G})\subseteq H^2(G,\mathbb{Z}/2\mathbb{Z})$$
    * We have $$\text{Br}\_{\mathcal{C}}BG = \widetilde{\text{Br}\_{\mathcal{C}}}BG/\left(\widetilde{\text{Br}\_{\mathcal{C}}}BG\cap V\times W\right)$$
Actually, since the Brauer group will be 2-torsion, we will not construct the quotient but instead take the orthogonal complement of $$\left(\widetilde{\text{Br}\_{\mathcal{C}}}BG\cap V\times W\right)$$ in $$\widetilde{\text{Br}\_{\mathcal{C}}}BG$$.
