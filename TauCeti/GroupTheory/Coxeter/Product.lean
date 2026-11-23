/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Graph
public import TauCeti.GroupTheory.Coxeter.Parabolic
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Coxeter groups of decomposable Coxeter matrices

Let `cs : CoxeterSystem M W` be a Coxeter system with simple reflections indexed by `B`, and let
`J ⊆ B` be a set of indices such that `M i j = 2` whenever `i ∈ J` and `j ∉ J`; that is, no edge of
the Coxeter graph `M.graph` joins `J` to its complement. Then `W` is the internal direct product of
the standard parabolic subgroups of `J` and of `Jᶜ`: every element of the first commutes with every
element of the second, and every `w : W` is a product `u * v` of an element `u` of the first and an
element `v` of the second for exactly one pair `(u, v)`.

More generally, a map `c : B → ι` to a finite type with `M i j = 2` whenever `c i ≠ c j` splits `W`
as the product of the standard parabolic subgroups of the fibres of `c`. Taking for `c` the map to
the connected components of the Coxeter graph shows that a Coxeter group with finitely many
components is the product of the parabolic subgroups of its components, and that its order is the
product of their orders. By `CoxeterSystem.parabolicHom_injective` and
`CoxeterSystem.range_parabolicHom` each factor is itself the Coxeter group of the restriction of
`M` to the corresponding set of indices.

The inverse of multiplication is not built from the intersection theorem for parabolic subgroups.
Instead, the Coxeter relations show that sending `s i` to itself for `i ∈ J` and to `1` otherwise
defines a retraction of `W` onto the standard parabolic subgroup of `J`; the retractions onto the
factors together invert multiplication.

## Main definitions

* `CoxeterSystem.parabolicProdComplMulEquiv`: multiplication identifies the product of the
  standard parabolic subgroups of `J` and of `Jᶜ` with `W`.
* `CoxeterSystem.piParabolicMulEquiv`: multiplication identifies the product of the standard
  parabolic subgroups of the fibres of `c : B → ι` with `W`.

## Main results

* `CoxeterSystem.commute_of_mem_parabolic_of_mem_parabolic_compl`: the two standard parabolic
  subgroups commute elementwise.
* `CoxeterSystem.isComplement'_parabolic_compl`: they are complements of each other.
* `CoxeterSystem.card_eq_prod_card_parabolic_supp`: the order of `W` is the product of the orders
  of the standard parabolic subgroups of the connected components of the Coxeter graph.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1, no. 9.
* M. W. Davis, *The Geometry and Topology of Coxeter Groups*, Princeton University Press (2008),
  Proposition 4.1.7.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- **Standard parabolic subgroups on either side of a cut of the Coxeter graph commute.** If
`M i j = 2` whenever `i ∈ J` and `j ∉ J`, every element of the standard parabolic subgroup of `J`
commutes with every element of the standard parabolic subgroup of `Jᶜ`. -/
theorem commute_of_mem_parabolic_of_mem_parabolic_compl {J : Set B}
    (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) {u v : W} (hu : u ∈ cs.parabolic J)
    (hv : v ∈ cs.parabolic Jᶜ) : Commute u v := by
  -- Each `s i` with `i ∈ J` centralizes the generators of the parabolic subgroup of `Jᶜ`.
  have hsimple : ∀ i ∈ J, cs.parabolic Jᶜ ≤ Subgroup.centralizer {cs.simple i} := fun i hi ↦
    (cs.parabolic_le_iff).mpr fun j hj ↦ Subgroup.mem_centralizer_singleton_iff.mpr
      (cs.commute_simple_of_eq_two (hJ i hi j hj)).eq.symm
  have hle : cs.parabolic J ≤ Subgroup.centralizer (cs.parabolic Jᶜ) :=
    (cs.parabolic_le_iff).mpr fun i hi ↦ Subgroup.mem_centralizer_iff.mpr fun _ hv ↦
      Subgroup.mem_centralizer_singleton_iff.mp (hsimple i hi hv)
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) v hv).symm

variable {J : Set B}

open Classical in
/-- The images of the simple reflections under the retraction onto the standard parabolic subgroup
of `J`: `s i` itself for `i ∈ J`, and `1` otherwise. -/
private noncomputable def retractionFun (J : Set B) (i : B) : cs.parabolic J :=
  if hi : i ∈ J then ⟨cs.simple i, cs.simple_mem_parabolic hi⟩ else 1

private theorem retractionFun_of_mem {i : B} (hi : i ∈ J) :
    cs.retractionFun J i = ⟨cs.simple i, cs.simple_mem_parabolic hi⟩ := by
  simp [retractionFun, hi]

private theorem retractionFun_of_notMem {i : B} (hi : i ∉ J) : cs.retractionFun J i = 1 := by
  simp [retractionFun, hi]

/-- The Coxeter relations between `J` and its complement hold in the retraction because the
corresponding entries of `M` are `2`. -/
private theorem isLiftable_retractionFun (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) :
    M.IsLiftable (cs.retractionFun J) := by
  intro i j
  by_cases hi : i ∈ J <;> by_cases hj : j ∈ J
  · rw [retractionFun_of_mem cs hi, retractionFun_of_mem cs hj]
    exact Subtype.ext (by simp)
  · rw [retractionFun_of_mem cs hi, retractionFun_of_notMem cs hj, mul_one, hJ i hi j hj]
    exact Subtype.ext (by simp)
  · rw [retractionFun_of_notMem cs hi, retractionFun_of_mem cs hj, one_mul, M.symmetric i j,
      hJ j hj i hi]
    exact Subtype.ext (by simp)
  · simp [retractionFun_of_notMem cs hi, retractionFun_of_notMem cs hj]

/-- The retraction of `W` onto the standard parabolic subgroup of `J` that fixes `s i` for `i ∈ J`
and kills `s j` for `j ∉ J`. -/
private noncomputable def parabolicRetraction (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) :
    W →* cs.parabolic J :=
  cs.lift ⟨cs.retractionFun J, cs.isLiftable_retractionFun hJ⟩

private theorem parabolicRetraction_simple_of_mem (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) {i : B}
    (hi : i ∈ J) :
    cs.parabolicRetraction hJ (cs.simple i) = ⟨cs.simple i, cs.simple_mem_parabolic hi⟩ := by
  rw [parabolicRetraction, lift_apply_simple, retractionFun_of_mem cs hi]

private theorem parabolicRetraction_simple_of_notMem (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) {i : B}
    (hi : i ∉ J) : cs.parabolicRetraction hJ (cs.simple i) = 1 := by
  rw [parabolicRetraction, lift_apply_simple, retractionFun_of_notMem cs hi]

/-- The retraction fixes the standard parabolic subgroup of `J`. -/
private theorem parabolicRetraction_comp_subtype (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) :
    (cs.parabolicRetraction hJ).comp (cs.parabolic J).subtype = MonoidHom.id _ :=
  cs.parabolic_hom_ext fun _ hi ↦ cs.parabolicRetraction_simple_of_mem hJ hi

/-- The retraction kills the standard parabolic subgroup of any set disjoint from `J`. -/
private theorem parabolicRetraction_comp_subtype_of_subset_compl
    (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2) {K : Set B} (hK : K ⊆ Jᶜ) :
    (cs.parabolicRetraction hJ).comp (cs.parabolic K).subtype = 1 :=
  cs.parabolic_hom_ext fun _ hi ↦ cs.parabolicRetraction_simple_of_notMem hJ (hK hi)

private theorem parabolicRetraction_apply_of_mem (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2)
    (u : cs.parabolic J) : cs.parabolicRetraction hJ u = u :=
  DFunLike.congr_fun (cs.parabolicRetraction_comp_subtype hJ) u

private theorem parabolicRetraction_apply_of_subset_compl (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2)
    {K : Set B} (hK : K ⊆ Jᶜ) (u : cs.parabolic K) : cs.parabolicRetraction hJ u = 1 :=
  DFunLike.congr_fun (cs.parabolicRetraction_comp_subtype_of_subset_compl hJ hK) u

/-! ### Splitting along a cut of the Coxeter graph -/

variable (hJ : ∀ i ∈ J, ∀ j ∉ J, M i j = 2)

include hJ in
/-- The hypothesis on `J` holds for `Jᶜ`, by symmetry of the Coxeter matrix. -/
private theorem compl_eq_two : ∀ i ∈ Jᶜ, ∀ j ∉ Jᶜ, M i j = 2 := fun i hi j hj ↦ by
  rw [M.symmetric]
  exact hJ j (not_not.mp hj) i hi

/-- **A cut of the Coxeter graph splits a Coxeter group.** If `M i j = 2` whenever `i ∈ J` and
`j ∉ J`, multiplication `(u, v) ↦ u * v` is an isomorphism from the product of the standard
parabolic subgroups of `J` and of `Jᶜ` onto `W`. -/
noncomputable def parabolicProdComplMulEquiv : cs.parabolic J × cs.parabolic Jᶜ ≃* W :=
  MonoidHom.toMulEquiv
    ((cs.parabolic J).subtype.noncommCoprod (cs.parabolic Jᶜ).subtype
      fun u v ↦ cs.commute_of_mem_parabolic_of_mem_parabolic_compl hJ u.property v.property)
    ((cs.parabolicRetraction hJ).prod (cs.parabolicRetraction (compl_eq_two hJ)))
    (MonoidHom.ext fun x ↦ by
      have h₁ := cs.parabolicRetraction_apply_of_mem hJ x.1
      have h₂ := cs.parabolicRetraction_apply_of_subset_compl hJ subset_rfl x.2
      have h₃ := cs.parabolicRetraction_apply_of_mem (compl_eq_two hJ) x.2
      have h₄ := cs.parabolicRetraction_apply_of_subset_compl (compl_eq_two hJ)
        (compl_compl J).symm.subset x.1
      ext <;> simp [h₁, h₂, h₃, h₄])
    (cs.ext_simple fun i ↦ by
      by_cases hi : i ∈ J
      · simp [cs.parabolicRetraction_simple_of_mem hJ hi,
          cs.parabolicRetraction_simple_of_notMem (compl_eq_two hJ) (not_not.mpr hi)]
      · simp [cs.parabolicRetraction_simple_of_notMem hJ hi,
          cs.parabolicRetraction_simple_of_mem (compl_eq_two hJ) hi])

/-- `CoxeterSystem.parabolicProdComplMulEquiv` multiplies the two factors. -/
@[simp]
theorem parabolicProdComplMulEquiv_apply (x : cs.parabolic J × cs.parabolic Jᶜ) :
    cs.parabolicProdComplMulEquiv hJ x = x.1 * x.2 := by
  rw [parabolicProdComplMulEquiv, MonoidHom.toMulEquiv_apply, MonoidHom.noncommCoprod_apply,
    Subgroup.coe_subtype, Subgroup.coe_subtype]

/-- The inverse of `CoxeterSystem.parabolicProdComplMulEquiv` sends `s i` with `i ∈ J` into the
first factor. -/
@[simp]
theorem parabolicProdComplMulEquiv_symm_simple_of_mem {i : B} (hi : i ∈ J) :
    (cs.parabolicProdComplMulEquiv hJ).symm (cs.simple i) =
      (⟨cs.simple i, cs.simple_mem_parabolic hi⟩, 1) := by
  rw [MulEquiv.symm_apply_eq]
  simp

/-- The inverse of `CoxeterSystem.parabolicProdComplMulEquiv` sends `s i` with `i ∉ J` into the
second factor. -/
@[simp]
theorem parabolicProdComplMulEquiv_symm_simple_of_notMem {i : B} (hi : i ∉ J) :
    (cs.parabolicProdComplMulEquiv hJ).symm (cs.simple i) =
      (1, ⟨cs.simple i, cs.simple_mem_parabolic (Set.mem_compl hi)⟩) := by
  rw [MulEquiv.symm_apply_eq]
  simp

include hJ in
/-- **The standard parabolic subgroups on either side of a cut of the Coxeter graph are
complements.** If `M i j = 2` whenever `i ∈ J` and `j ∉ J`, every element of `W` is a product
`u * v` of an element `u` of the standard parabolic subgroup of `J` and an element `v` of that of
`Jᶜ`, for exactly one such pair. -/
theorem isComplement'_parabolic_compl : (cs.parabolic J).IsComplement' (cs.parabolic Jᶜ) :=
  (cs.parabolicProdComplMulEquiv hJ).bijective

/-! ### Splitting along a partition of the indices -/

variable {ι : Type*} (c : B → ι) (hc : ∀ i j, c i ≠ c j → M i j = 2)

include hc in
/-- The hypothesis of the cut splitting holds for every fibre of `c`. -/
private theorem preimage_singleton_eq_two (k : ι) :
    ∀ i ∈ c ⁻¹' {k}, ∀ j ∉ c ⁻¹' {k}, M i j = 2 := fun i hi j hj ↦
  hc i j fun h ↦ hj (by simpa [← h] using hi)

include hc in
/-- Standard parabolic subgroups of distinct fibres of `c` commute elementwise. -/
theorem commute_of_mem_parabolic_preimage_singleton {k l : ι} (hkl : k ≠ l) {u v : W}
    (hu : u ∈ cs.parabolic (c ⁻¹' {k})) (hv : v ∈ cs.parabolic (c ⁻¹' {l})) : Commute u v :=
  have hsub : c ⁻¹' {l} ⊆ (c ⁻¹' {k})ᶜ := fun _ hi hi' ↦ hkl (by simp_all)
  cs.commute_of_mem_parabolic_of_mem_parabolic_compl (preimage_singleton_eq_two c hc k) hu
    (cs.parabolic_mono hsub hv)

include hc in
private theorem pairwise_commute_parabolic_preimage_singleton :
    Pairwise fun k l ↦ ∀ u v : W, u ∈ cs.parabolic (c ⁻¹' {k}) → v ∈ cs.parabolic (c ⁻¹' {l}) →
      Commute u v :=
  fun _ _ hkl _ _ ↦ cs.commute_of_mem_parabolic_preimage_singleton c hc hkl

/-- The product of the retractions onto the fibres of `c` sends `s i` into the factor of `c i`. -/
private theorem pi_parabolicRetraction_simple [DecidableEq ι] (i : B) :
    MonoidHom.pi (fun k ↦ cs.parabolicRetraction (preimage_singleton_eq_two c hc k))
      (cs.simple i) = Pi.mulSingle (c i)
        ⟨cs.simple i, cs.simple_mem_parabolic (Set.mem_preimage.mpr (Set.mem_singleton _))⟩ := by
  funext k
  rw [MonoidHom.pi_apply]
  by_cases hk : c i = k
  · subst hk
    rw [Pi.mulSingle_eq_same, parabolicRetraction_simple_of_mem _ _ rfl]
  · rw [Pi.mulSingle_eq_of_ne' hk, parabolicRetraction_simple_of_notMem _ _ hk]

/-- **A partition of the indices with no edges between its parts splits a Coxeter group.** If
`c : B → ι` maps to a finite type and `M i j = 2` whenever `c i ≠ c j`, multiplication is an
isomorphism from the product of the standard parabolic subgroups of the fibres of `c` onto `W`.
Applied to the connected components of the Coxeter graph
(`CoxeterMatrix.eq_two_of_connectedComponentMk_ne`), this splits `W` as the product of the
standard parabolic subgroups of the components. -/
noncomputable def piParabolicMulEquiv [Fintype ι] :
    (∀ k, cs.parabolic (c ⁻¹' {k})) ≃* W := by
  classical
  exact MonoidHom.toMulEquiv
    (Subgroup.noncommPiCoprod (cs.pairwise_commute_parabolic_preimage_singleton c hc))
    (MonoidHom.pi fun k ↦ cs.parabolicRetraction (preimage_singleton_eq_two c hc k))
    (MonoidHom.pi_ext fun k u ↦ funext fun l ↦ by
      simp only [MonoidHom.comp_apply, Subgroup.noncommPiCoprod_mulSingle, MonoidHom.pi_apply,
        MonoidHom.id_apply]
      by_cases hkl : k = l
      · subst hkl
        rw [Pi.mulSingle_eq_same, parabolicRetraction_apply_of_mem]
      · rw [Pi.mulSingle_eq_of_ne' hkl, parabolicRetraction_apply_of_subset_compl]
        exact fun _ hi hi' ↦ hkl (by simp_all))
    (cs.ext_simple fun i ↦ by
      rw [MonoidHom.comp_apply, cs.pi_parabolicRetraction_simple c hc,
        Subgroup.noncommPiCoprod_mulSingle, MonoidHom.id_apply])

/-- `CoxeterSystem.piParabolicMulEquiv` is the inclusion on each factor. -/
@[simp]
theorem piParabolicMulEquiv_mulSingle [Fintype ι] [DecidableEq ι] (k : ι)
    (u : cs.parabolic (c ⁻¹' {k})) : cs.piParabolicMulEquiv c hc (Pi.mulSingle k u) = u := by
  rw [piParabolicMulEquiv, MonoidHom.toMulEquiv_apply]
  exact Subgroup.noncommPiCoprod_mulSingle (H := fun k ↦ cs.parabolic (c ⁻¹' {k})) k u

/-- The inverse of `CoxeterSystem.piParabolicMulEquiv` sends `s i` into the factor of `c i`. -/
@[simp]
theorem piParabolicMulEquiv_symm_simple [Fintype ι] [DecidableEq ι] (i : B) :
    (cs.piParabolicMulEquiv c hc).symm (cs.simple i) = Pi.mulSingle (c i)
      ⟨cs.simple i, cs.simple_mem_parabolic (Set.mem_preimage.mpr (Set.mem_singleton _))⟩ := by
  rw [MulEquiv.symm_apply_eq, piParabolicMulEquiv_mulSingle]

/-- **The order of a Coxeter group is the product of the orders of its components.** If the
Coxeter graph has finitely many connected components, the order of `W` is the product of the
orders of the standard parabolic subgroups of the components. Both sides are `0` when `W` is
infinite. -/
theorem card_eq_prod_card_parabolic_supp [Fintype M.graph.ConnectedComponent] :
    Nat.card W = ∏ K : M.graph.ConnectedComponent, Nat.card (cs.parabolic K.supp) := by
  rw [← Nat.card_congr
    (cs.piParabolicMulEquiv _ fun _ _ ↦ M.eq_two_of_connectedComponentMk_ne).toEquiv,
    Nat.card_pi]
  have h (K : M.graph.ConnectedComponent) : M.graph.connectedComponentMk ⁻¹' {K} = K.supp := by
    ext v
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  simp only [h]

end CoxeterSystem
