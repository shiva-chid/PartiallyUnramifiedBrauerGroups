# Brauer Groups of BG

## Guide to Repo
This repo currently contains some code we wrote at ICERM in the number field counting programme in 2026.  We are currently working through it to check correctness, as well as conclude a proper implementation of the Brauer group.

## Algorithm
At present, `main.mg` presents an overgroup $$\tilde{B}_{\mathcal{C},G}$$ of the Brauer group $$\text{Br}_{\mathcal{C}}^eBG$$.  This satisfies the Following properties
    - $$\tilde{B}_{\mathcal{C},G}\subseteq H^1(\mathbb{Q}(\zeta_{2|G|})/\mathbb{Q}, \hat{G}[2])\times H^2(G, \mathbb{Z}/2\mathbb{Z})$$.
    - There is a short exact sequence
    $$1\to \hat{G}/2\hat{G}\to \tilde{B}_{\mathcal{C},G}\to \text{Br}_{\mathcal{C}}^eBG\to 0$$
It also gives maps which take elements of this abstract groups and return the coordinates as homomorphisms (respectively extension classes).

## Acknowledgements
ChatGPT has been used for bug checking and general assistance, but all code is written and checked by the humans.