/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Cohomology.Flag
public import TauCeti.GroupTheory.ConedOffCayleyGraph
public import TauCeti.GroupTheory.RelativelyFinitelyPresented
import Mathlib.GroupTheory.RegularWreathProduct

/-!
# The flag complex of the coned-off Cayley graph of a relative presentation

Let `G` be finitely presented relative to a family `ℋ` of subgroups: for a finite family `Ω` of
elements of `G`, the natural homomorphism `F(Ω) ∗ (∗_{H ∈ ℋ} H) → G` is onto and its kernel is
the normal closure of a finite set `R` of relators. Guirardel and Levitt realise `G` as the
fundamental group of a two-complex: complexes `Y_H` with fundamental group `H`, joined by an edge
to a vertex `u`, a loop at `u` for each element of `Ω`, and a disc glued along each relator. In its
universal cover the lifts of `Y_H` correspond to the left cosets `g H`.

The coned-off Cayley graph `TauCeti.Group.conedOffCayleyGraph A ℋ` replaces this universal cover
in Dunwoody's track arguments: every lift of `Y_H` is coned off to the vertex `g H`, and every
relator disc is triangulated by a fan of triangles. For this, `A` is taken to consist of the
images of the generators in `Ω`, of the letters (generators, their inverses and elements of the
subgroups in `ℋ`) and of all prefixes of words representing the relators. The main result is that
for some finite `A` the graph is connected and the first cohomology of its flag complex vanishes,
for every coefficient group: with coefficients `ℤ/2` this is the hypothesis `H¹(K; ℤ/2) = 0` of
Dunwoody's almost finitely presented groups, under which every track separates.

## Main results

* `IsFinitelyPresentedRel.exists_finite_hasTrivialFlagFirstCohomology_conedOffCayleyGraph`:
  if `G` is finitely presented relative to `ℋ`, then for some finite `A` the coned-off Cayley graph
  is connected and the first cohomology of its flag complex vanishes with every coefficient group.

## Implementation notes

A cocycle `z` with values in `M` is integrated along the words of `F(Ω) ∗ (∗_{H ∈ ℋ} H)`: reading
a word from a vertex `g` adds up the values of `z` along the corresponding path, a letter of a
subgroup `H` being read through the cone vertex `g H`. The values for all starting points and the
image in `G` form a homomorphism to the regular wreath product `Multiplicative M ≀ᵣ G`. Along a word
whose letters and prefixes have images in `A`, the integral from `g` is the value of `z` on the
edge from `g` to the endpoint, by the cocycle relation on the triangles of the fan; so the
homomorphism kills the relators, hence the kernel of the natural homomorphism, and the integral
from `1` is a potential for `z`.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §2.5: the
  two-complex of a relative finite presentation, before the proof of Proposition 2.24.
* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457, §1 (almost finitely presented groups).
-/

public section

namespace TauCeti

namespace Group

open Function Monoid

variable {G : Type*} [Group G] {A : Set G} {ℋ : Set (Subgroup G)} {M : Type*} [AddCommGroup M]
  {z : ConedOffCayleyVertex ℋ → ConedOffCayleyVertex ℋ → M} {α : Type*} {φ : FreeGroup α →* G}

/-! ### Cocycles of the flag complex, extended by zero -/

variable (A) in
/- A cocycle of the flag complex of the coned-off Cayley graph with coefficients in `M`. -/
private def IsCocycle (z : ConedOffCayleyVertex ℋ → ConedOffCayleyVertex ℋ → M) : Prop :=
  (∀ u v, (conedOffCayleyGraph A ℋ).Adj u v → z v u = -z u v) ∧
    ∀ u v w, (conedOffCayleyGraph A ℋ).Adj u v → (conedOffCayleyGraph A ℋ).Adj v w →
      (conedOffCayleyGraph A ℋ).Adj u w → z u v + z v w = z u w

variable (A) in
/- `z` on the edges of the coned-off Cayley graph and `0` elsewhere. -/
private noncomputable def edgeCochain (z : ConedOffCayleyVertex ℋ → ConedOffCayleyVertex ℋ → M)
    (u v : ConedOffCayleyVertex ℋ) : M :=
  open Classical in if (conedOffCayleyGraph A ℋ).Adj u v then z u v else 0

private theorem edgeCochain_of_adj {u v : ConedOffCayleyVertex ℋ}
    (h : (conedOffCayleyGraph A ℋ).Adj u v) : edgeCochain A z u v = z u v := by
  simp [edgeCochain, h]

@[simp]
private theorem edgeCochain_self (u : ConedOffCayleyVertex ℋ) : edgeCochain A z u u = 0 := by
  simp [edgeCochain]

private theorem IsCocycle.edgeCochain_swap (hz : IsCocycle A z) (u v : ConedOffCayleyVertex ℋ) :
    edgeCochain A z v u = -edgeCochain A z u v := by
  by_cases h : (conedOffCayleyGraph A ℋ).Adj u v
  · rw [edgeCochain_of_adj h, edgeCochain_of_adj h.symm, hz.1 u v h]
  · simp [edgeCochain, h, SimpleGraph.adj_comm]

/- The cocycle relation for three vertices which are pairwise equal or adjacent. -/
private theorem IsCocycle.edgeCochain_add (hz : IsCocycle A z) {u v w : ConedOffCayleyVertex ℋ}
    (huv : u = v ∨ (conedOffCayleyGraph A ℋ).Adj u v)
    (hvw : v = w ∨ (conedOffCayleyGraph A ℋ).Adj v w)
    (huw : u = w ∨ (conedOffCayleyGraph A ℋ).Adj u w) :
    edgeCochain A z u v + edgeCochain A z v w = edgeCochain A z u w := by
  rcases huv with rfl | huv
  · simp
  rcases hvw with rfl | hvw
  · simp
  rcases huw with rfl | huw
  · rw [hz.edgeCochain_swap u v, add_neg_cancel, edgeCochain_self]
  rw [edgeCochain_of_adj huv, edgeCochain_of_adj hvw, edgeCochain_of_adj huw,
    hz.2 u v w huv hvw huw]

private theorem eq_or_adj_of_mem_insert {a : G} (ha : a ∈ insert 1 A) (g : G) :
    (.inl g : ConedOffCayleyVertex ℋ) = .inl (g * a) ∨
      (conedOffCayleyGraph A ℋ).Adj (.inl g) (.inl (g * a)) := by
  by_cases h1 : a = 1
  · simp [h1]
  exact .inr (conedOffCayleyGraph_adj_inl_inl.2 ⟨by simpa using h1,
    .inl (by simpa using (Set.mem_insert_iff.1 ha).resolve_left h1)⟩)

/-! ### Integrating a cochain along words -/

variable (A z) in
/- Integration of `z` along the words of `F(α) ∗ (∗_{H ∈ ℋ} H)`. The value at a word `w` is the
image of `w` in `G` together with the function sending `x` to the sum of `z` along the path read
from `x⁻¹`: a generator `ω` is the step from `g` to `g ω`, an element `h` of `H ∈ ℋ` is the path
from `g` through the coset `g H` to `g h`. -/
private noncomputable def costHom (φ : FreeGroup α →* G) :
    RelFreeProduct α ℋ →* Multiplicative M ≀ᵣ G :=
  Coprod.lift (FreeGroup.lift fun i ↦
      ⟨fun x ↦ .ofAdd (edgeCochain A z (.inl x⁻¹) (.inl (x⁻¹ * φ (.of i)))), φ (.of i)⟩)
    (CoprodI.lift fun H ↦ (MulAut.conj (⟨fun x ↦ .ofAdd (edgeCochain A z (.inl x⁻¹)
      (.inr ⟨H, (x⁻¹ : G)⟩)), 1⟩ : Multiplicative M ≀ᵣ G)).toMonoidHom.comp
        (RegularWreathProduct.inl.comp (H : Subgroup G).subtype))

private theorem costHom_right (w : RelFreeProduct α ℋ) :
    (costHom A z φ w).right = relPresentationHom φ ℋ w := by
  have : RegularWreathProduct.rightHom.comp (costHom A z φ) = relPresentationHom φ ℋ := by
    ext <;> simp [costHom]
  exact DFunLike.congr_fun this w

private theorem costHom_inl_of_left (i : α) (x : G) :
    (costHom A z φ (Coprod.inl (.of i))).left x =
      .ofAdd (edgeCochain A z (.inl x⁻¹) (.inl (x⁻¹ * φ (.of i)))) := by
  simp [costHom]

private theorem costHom_inr_of_left {H : ℋ} (h : (H : Subgroup G)) (x : G) :
    (costHom A z φ (Coprod.inr (CoprodI.of h))).left x =
      .ofAdd (edgeCochain A z (.inl x⁻¹) (.inr ⟨H, (x⁻¹ : G)⟩) -
        edgeCochain A z (.inl (x⁻¹ * h)) (.inr ⟨H, (x⁻¹ : G)⟩)) := by
  simp [costHom, div_eq_mul_inv]

variable (A z φ) in
/- A word is *direct* when its integral from every vertex `g` is the value of the cochain on the
pair `(g, g ρ(w))`, for `ρ` the natural homomorphism to `G`. -/
private def IsDirect (w : RelFreeProduct α ℋ) : Prop :=
  ∀ x : G, (costHom A z φ w).left x =
    .ofAdd (edgeCochain A z (.inl x⁻¹) (.inl (x⁻¹ * relPresentationHom φ ℋ w)))

private theorem isDirect_one : IsDirect A z φ 1 := fun _ ↦ by
  simp

private theorem isDirect_inl_of (i : α) : IsDirect A z φ (Coprod.inl (.of i)) := fun _ ↦ by
  simp [costHom_inl_of_left]

private theorem IsDirect.inv (hz : IsCocycle A z) {w : RelFreeProduct α ℋ} (hw : IsDirect A z φ w) :
    IsDirect A z φ w⁻¹ := fun x ↦ by
  simp [hw _, costHom_right, hz.edgeCochain_swap (.inl x⁻¹)]

private theorem isDirect_inr_of (hz : IsCocycle A z) {H : ℋ} {h : (H : Subgroup G)}
    (hh : (h : G) ∈ insert 1 A) : IsDirect A z φ (Coprod.inr (CoprodI.of h)) := fun x ↦ by
  rw [costHom_inr_of_left, relPresentationHom_inr_of, sub_eq_add_neg, ← hz.edgeCochain_swap,
    hz.edgeCochain_add (.inr ?_) (.inr ?_) (eq_or_adj_of_mem_insert hh _)] <;> simp

/- The product of two direct words is direct when the images of the two words and of their
product lie in `A ∪ {1}`: the three steps bound a triangle. -/
private theorem IsDirect.mul (hz : IsCocycle A z) {w w' : RelFreeProduct α ℋ}
    (hw : IsDirect A z φ w) (hw' : IsDirect A z φ w') (h₁ : relPresentationHom φ ℋ w ∈ insert 1 A)
    (h₂ : relPresentationHom φ ℋ w' ∈ insert 1 A)
    (h₁₂ : relPresentationHom φ ℋ (w * w') ∈ insert 1 A) : IsDirect A z φ (w * w') := fun x ↦ by
  rw [map_mul] at h₁₂
  have h₂' := eq_or_adj_of_mem_insert (ℋ := ℋ) h₂ (x⁻¹ * relPresentationHom φ ℋ w)
  rw [mul_assoc] at h₂'
  simp [hw _, hw' _, costHom_right, ← ofAdd_add, mul_assoc,
    hz.edgeCochain_add (eq_or_adj_of_mem_insert h₁ x⁻¹) h₂' (eq_or_adj_of_mem_insert h₁₂ x⁻¹)]

/-! ### Words along fans of triangles -/

variable (α ℋ) in
/- The letters of `F(α) ∗ (∗_{H ∈ ℋ} H)`: the free generators, their inverses and the elements of
the subgroups in the family. -/
private def letters : Set (RelFreeProduct α ℋ) :=
  {x | ∃ i, x = Coprod.inl (.of i) ∨ x = (Coprod.inl (.of i))⁻¹} ∪
    {x | ∃ (H : ℋ) (h : (H : Subgroup G)), x = (Coprod.inr (CoprodI.of h) : RelFreeProduct α ℋ)}

private theorem closure_letters : Submonoid.closure (letters ℋ α) = ⊤ := by
  refine (Submonoid.eq_top_iff' _).2 fun w ↦ ?_
  induction w using Coprod.induction_on with
  | inl m =>
    induction m using FreeGroup.induction_on with
    | one => simp
    | of i => exact Submonoid.subset_closure (.inl ⟨i, .inl rfl⟩)
    | inv_of i => exact Submonoid.subset_closure (.inl ⟨i, .inr (map_inv _ _)⟩)
    | mul x y hx hy => simpa using mul_mem hx hy
  | inr n =>
    induction n using CoprodI.induction_on with
    | one => simp
    | of i h => exact Submonoid.subset_closure (.inr ⟨i, h, rfl⟩)
    | mul x y hx hy => simpa using mul_mem hx hy
  | mul x y hx hy => exact mul_mem hx hy

private theorem isDirect_of_mem_letters (hz : IsCocycle A z) {x : RelFreeProduct α ℋ}
    (hx : x ∈ letters ℋ α) (hA : relPresentationHom φ ℋ x ∈ insert 1 A) : IsDirect A z φ x := by
  rcases hx with ⟨i, rfl | rfl⟩ | ⟨H, h, rfl⟩
  · exact isDirect_inl_of i
  · exact (isDirect_inl_of i).inv hz
  · exact isDirect_inr_of hz (by simpa using hA)

private theorem IsDirect.mul_prod (hz : IsCocycle A z) {l : List (RelFreeProduct α ℋ)}
    {w : RelFreeProduct α ℋ} (hw : IsDirect A z φ w)
    (hl : ∀ x ∈ l, x ∈ letters ℋ α ∧ relPresentationHom φ ℋ x ∈ insert 1 A)
    (hp : ∀ p, p <+: l → relPresentationHom φ ℋ (w * p.prod) ∈ insert 1 A) :
    IsDirect A z φ (w * l.prod) := by
  induction l generalizing w with
  | nil => simpa using hw
  | cons x l ih =>
    rw [List.prod_cons, ← mul_assoc]
    have hx := hl x List.mem_cons_self
    refine ih (hw.mul hz (isDirect_of_mem_letters hz hx.1 hx.2)
        (by simpa using hp [] List.nil_prefix) hx.2 (by simpa using hp [x] (by simp)))
      (fun y hy ↦ hl y (List.mem_cons_of_mem _ hy)) fun p hp' ↦ ?_
    simpa [mul_assoc] using hp (x :: p) (List.cons_prefix_cons.2 ⟨rfl, hp'⟩)

variable (A φ) in
/- A list of letters whose letters and prefixes all have images in `A ∪ {1}`: reading its
product from `g` runs along a fan of triangles with apex `g`. -/
private def IsFan (l : List (RelFreeProduct α ℋ)) : Prop :=
  (∀ x ∈ l, x ∈ letters ℋ α ∧ relPresentationHom φ ℋ x ∈ insert 1 A) ∧
    ∀ p, p <+: l → relPresentationHom φ ℋ p.prod ∈ insert 1 A

private theorem IsFan.isDirect (hz : IsCocycle A z) {l : List (RelFreeProduct α ℋ)}
    (hl : IsFan A φ l) : IsDirect A z φ l.prod := by
  simpa using isDirect_one.mul_prod hz hl.1 (by simpa using hl.2)

private theorem IsFan.of_prefix {l p : List (RelFreeProduct α ℋ)} (hl : IsFan A φ l)
    (hp : p <+: l) : IsFan A φ p :=
  ⟨fun x hx ↦ hl.1 x (hp.subset hx), fun q hq ↦ hl.2 q (hq.trans hp)⟩

private theorem isFan_singleton {x : RelFreeProduct α ℋ} (hx : x ∈ letters ℋ α)
    (hA : relPresentationHom φ ℋ x ∈ insert 1 A) : IsFan A φ [x] :=
  ⟨by simpa using ⟨hx, hA⟩, fun p hp ↦ by
    rcases List.prefix_cons_iff.1 hp with rfl | ⟨t, rfl, ht⟩
    · simp
    · simpa [List.prefix_nil.1 ht] using hA⟩

/- If the relators are products along fans, the integral of a word depends only on its image
in `G`. -/
private theorem IsCocycle.costHom_eq (hz : IsCocycle A z) {S : Set (RelFreeProduct α ℋ)}
    (hS : Subgroup.normalClosure S = (relPresentationHom φ ℋ).ker)
    (hrel : ∀ s ∈ S, ∃ l, IsFan A φ l ∧ l.prod = s) {w w' : RelFreeProduct α ℋ}
    (h : relPresentationHom φ ℋ w = relPresentationHom φ ℋ w') :
    costHom A z φ w = costHom A z φ w' := by
  have hker : (relPresentationHom φ ℋ).ker ≤ (costHom A z φ).ker :=
    hS ▸ Subgroup.normalClosure_le_normal fun s hs ↦ by
      have h1 : relPresentationHom φ ℋ s = 1 :=
        MonoidHom.mem_ker.1 (hS ▸ Subgroup.subset_normalClosure hs)
      obtain ⟨l, hl, rfl⟩ := hrel s hs
      ext x
      · simp [hl.isDirect hz x, h1]
      · simp [costHom_right, h1]
  exact (MonoidHom.eq_iff _).2 (hker ((MonoidHom.eq_iff _).1 h))

/-! ### The potential -/

variable (A z) in
/- The integral of `z` along a word representing `g`, read from `1`. -/
private noncomputable def potential (hρ : Surjective (relPresentationHom φ ℋ)) (g : G) : M :=
  Multiplicative.toAdd ((costHom A z φ (surjInv hρ g)).left 1)

variable (A z) in
/- The potential on all vertices: at the coset `g H` it is the potential at `g` plus the value of
the cochain on the edge from `g` to `g H`. -/
private noncomputable def vertexPotential (hρ : Surjective (relPresentationHom φ ℋ)) :
    ConedOffCayleyVertex ℋ → M
  | .inl g => potential A z hρ g
  | .inr q => potential A z hρ q.2.out + edgeCochain A z (.inl q.2.out) (.inr q)

private theorem potential_mul (hρ : Surjective (relPresentationHom φ ℋ))
    (hΨ : ∀ w w', relPresentationHom φ ℋ w = relPresentationHom φ ℋ w' →
      costHom A z φ w = costHom A z φ w') (g : G) (w : RelFreeProduct α ℋ) :
    potential A z hρ (g * relPresentationHom φ ℋ w) =
      potential A z hρ g + Multiplicative.toAdd ((costHom A z φ w).left g⁻¹) := by
  rw [potential, hΨ _ (surjInv hρ g * w) (by rw [surjInv_eq hρ, map_mul, surjInv_eq hρ])]
  simp [costHom_right, surjInv_eq, potential]

private theorem potential_eq_of_mem (hz : IsCocycle A z)
    (hρ : Surjective (relPresentationHom φ ℋ))
    (hΨ : ∀ w w', relPresentationHom φ ℋ w = relPresentationHom φ ℋ w' →
      costHom A z φ w = costHom A z φ w')
    (hA : ∀ a ∈ A, ∃ l, IsFan A φ l ∧ relPresentationHom φ ℋ l.prod = a) {g g' : G}
    (ha : g⁻¹ * g' ∈ A) :
    potential A z hρ g' = potential A z hρ g + edgeCochain A z (.inl g) (.inl g') := by
  obtain ⟨l, hl, hl'⟩ := hA _ ha
  simpa [hl', hl.isDirect hz g⁻¹] using potential_mul hρ hΨ g l.prod

private theorem vertexPotential_inr (hρ : Surjective (relPresentationHom φ ℋ))
    (hΨ : ∀ w w', relPresentationHom φ ℋ w = relPresentationHom φ ℋ w' →
      costHom A z φ w = costHom A z φ w') (H : ℋ) (g : G) :
    vertexPotential A z hρ (.inr ⟨H, g⟩) =
      potential A z hρ g + edgeCochain A z (.inl g) (.inr ⟨H, g⟩) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H : Subgroup G) g
  have := potential_mul hρ hΨ g (Coprod.inr (CoprodI.of h))
  rw [relPresentationHom_inr_of, costHom_inr_of_left] at this
  simp only [inv_inv, toAdd_ofAdd] at this
  simp only [vertexPotential, hh, this, add_assoc, sub_add_cancel]

private theorem IsCocycle.eq_vertexPotential_sub (hz : IsCocycle A z)
    (hρ : Surjective (relPresentationHom φ ℋ))
    (hΨ : ∀ w w', relPresentationHom φ ℋ w = relPresentationHom φ ℋ w' →
      costHom A z φ w = costHom A z φ w')
    (hA : ∀ a ∈ A, ∃ l, IsFan A φ l ∧ relPresentationHom φ ℋ l.prod = a)
    {u v : ConedOffCayleyVertex ℋ} (huv : (conedOffCayleyGraph A ℋ).Adj u v) :
    z u v = vertexPotential A z hρ v - vertexPotential A z hρ u := by
  rcases u with g | ⟨H, q⟩ <;> rcases v with g' | ⟨H', q'⟩
  · rcases (conedOffCayleyGraph_adj_inl_inl.1 huv).2 with ha | ha
    · simp [vertexPotential, potential_eq_of_mem hz hρ hΨ hA ha, edgeCochain_of_adj huv]
    · simp [vertexPotential, potential_eq_of_mem hz hρ hΨ hA ha, edgeCochain_of_adj huv.symm,
        hz.1 _ _ huv.symm]
  · obtain rfl := conedOffCayleyGraph_adj_inl_inr.1 huv
    rw [vertexPotential_inr hρ hΨ]
    simp [vertexPotential, edgeCochain_of_adj huv]
  · obtain rfl := conedOffCayleyGraph_adj_inr_inl.1 huv
    rw [vertexPotential_inr hρ hΨ]
    simp [vertexPotential, edgeCochain_of_adj huv.symm, hz.1 _ _ huv.symm]
  · exact (not_conedOffCayleyGraph_adj_inr_inr huv).elim

/- If the relators and the elements of `A` are products along fans, the first cohomology of the
flag complex of the coned-off Cayley graph vanishes. -/
private theorem hasTrivialFlagFirstCohomology_of_isFan (hρ : Surjective (relPresentationHom φ ℋ))
    {S : Set (RelFreeProduct α ℋ)} (hS : Subgroup.normalClosure S = (relPresentationHom φ ℋ).ker)
    (hrel : ∀ s ∈ S, ∃ l, IsFan A φ l ∧ l.prod = s)
    (hA : ∀ a ∈ A, ∃ l, IsFan A φ l ∧ relPresentationHom φ ℋ l.prod = a) :
    (conedOffCayleyGraph A ℋ).HasTrivialFlagFirstCohomology M :=
  SimpleGraph.hasTrivialFlagFirstCohomology_iff.2 fun z hanti hcoc ↦
    have hz : IsCocycle A z := ⟨hanti, hcoc⟩
    ⟨vertexPotential A z hρ, fun _ _ huv ↦
      hz.eq_vertexPotential_sub hρ (fun _ _ ↦ hz.costHom_eq hS hrel) hA huv⟩

/- The coned-off Cayley graph is connected when `A` contains the images of the generators of
a relative generating family. -/
private theorem connected_conedOffCayleyGraph (hρ : Surjective (relPresentationHom φ ℋ))
    (hA : ∀ i, φ (.of i) ∈ A) : (conedOffCayleyGraph A ℋ).Connected := by
  refine conedOffCayleyGraph_connected_iff.2 (eq_top_iff.2 ?_)
  rw [← relPresentationHom_surjective_iff.1 hρ]
  refine sup_le_sup_right ?_ _
  rw [MonoidHom.range_eq_map, ← FreeGroup.closure_range_of, MonoidHom.map_closure]
  exact Subgroup.closure_mono (Set.image_subset_iff.2 fun _ ⟨i, hi⟩ ↦ hi ▸ hA i)

/- For a finite set of relators, a finite set `A` containing the images of the generators, such
that every relator and every element of `A` is a product along a fan: the images of the
generators and of the letters and prefixes of words representing the relators. -/
private theorem exists_finite_isFan {n : ℕ} {φ : FreeGroup (Fin n) →* G}
    {S : Set (RelFreeProduct (Fin n) ℋ)} (hS : S.Finite) :
    ∃ A : Set G, A.Finite ∧ (∀ i, φ (.of i) ∈ A) ∧ (∀ s ∈ S, ∃ l, IsFan A φ l ∧ l.prod = s) ∧
      ∀ a ∈ A, ∃ l, IsFan A φ l ∧ relPresentationHom φ ℋ l.prod = a := by
  -- write every relator as a product of letters; `A` is the image of the following words
  choose l hl hlprod using fun s ↦ Submonoid.exists_list_of_mem_closure
    ((closure_letters (ℋ := ℋ) (α := Fin n)).symm ▸ Submonoid.mem_top s)
  let D : Set (RelFreeProduct (Fin n) ℋ) := Set.range (fun i ↦ Coprod.inl (.of i)) ∪
    ⋃ s ∈ S, ({x | x ∈ l s} ∪ List.prod '' {p | p <+: l s})
  have hD {x} (hx : x ∈ D) : relPresentationHom φ ℋ x ∈ insert 1 (relPresentationHom φ ℋ '' D) :=
    Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hx)
  have hfan (s) (hs : s ∈ S) : IsFan (relPresentationHom φ ℋ '' D) φ (l s) :=
    ⟨fun x hx ↦ ⟨hl s x hx, hD (.inr (Set.mem_biUnion hs (.inl hx)))⟩,
      fun p hp ↦ hD (.inr (Set.mem_biUnion hs (.inr ⟨p, hp, rfl⟩)))⟩
  refine ⟨relPresentationHom φ ℋ '' D, ?_, fun i ↦ ⟨_, .inl ⟨i, rfl⟩, by simp⟩,
    fun s hs ↦ ⟨l s, hfan s hs, hlprod s⟩, ?_⟩
  · refine ((Set.finite_range _).union (hS.biUnion fun s _ ↦ (List.finite_toSet _).union
      (((List.finite_toSet (l s).inits).subset fun p hp ↦ ?_).image List.prod))).image _
    exact (List.mem_inits _ _).2 hp
  rintro _ ⟨d, hd, rfl⟩
  rcases hd with ⟨i, rfl⟩ | hd
  · exact ⟨[Coprod.inl (.of i)], isFan_singleton (.inl ⟨i, .inl rfl⟩) (hD (.inl ⟨i, rfl⟩)),
      by simp⟩
  obtain ⟨s, hs, hx | ⟨p, hp, rfl⟩⟩ := Set.mem_iUnion₂.1 hd
  · exact ⟨[d], isFan_singleton (hl s d hx) (hD (.inr (Set.mem_biUnion hs (.inl hx)))), by simp⟩
  · exact ⟨p, (hfan s hs).of_prefix hp, rfl⟩

namespace IsFinitelyPresentedRel

/-- **The two-complex of a relative finite presentation.** If `G` is finitely presented relative
to `ℋ`, then there is a finite set `A` of elements of `G` for which the coned-off Cayley graph is
connected and the first cohomology of its flag complex vanishes, with every coefficient group. -/
theorem exists_finite_hasTrivialFlagFirstCohomology_conedOffCayleyGraph
    (h : IsFinitelyPresentedRel ℋ) :
    ∃ A : Set G, A.Finite ∧ (conedOffCayleyGraph A ℋ).Connected ∧ ∀ (M : Type*) [AddCommGroup M],
      (conedOffCayleyGraph A ℋ).HasTrivialFlagFirstCohomology M := by
  obtain ⟨n, φ, hρ, S, hSfin, hS⟩ := isFinitelyPresentedRel_iff.1 h
  obtain ⟨A, hA, hgen, hrel, hfan⟩ := exists_finite_isFan (φ := φ) hSfin
  exact ⟨A, hA, connected_conedOffCayleyGraph hρ hgen,
    fun _ _ ↦ hasTrivialFlagFirstCohomology_of_isFan hρ hS hrel hfan⟩

end IsFinitelyPresentedRel

end Group

end TauCeti
