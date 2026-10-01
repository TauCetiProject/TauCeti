/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.Atoms.Finite
import TauCeti.GroupTheory.PGroup
import TauCeti.Topology.Algebra.Group.Generation
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Step
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic

/-!
# Burnside generation for pro-`p` groups

For a pro-`p` group, the Frattini subgroup detects topological generation. A closed subgroup
which is not contained in any open normal subgroup of index `p` is the whole group, and hence a
set topologically generates the group exactly when its image topologically generates the
Frattini quotient.

The finite input is that a maximal subgroup of a finite `p`-group has index `p`. To apply it to a
proper closed subgroup `H` of a profinite pro-`p` group, first choose an open normal subgroup `U`
for which `H ⊔ U` is still proper. The image of `H` in the finite `p`-group `G/U` lies in a
maximal subgroup. Its pullback is an open normal subgroup of index `p` containing `H`.

As a consequence, a **Frattini cover** `φ : G → H` of a pro-`p` group `G`, that is a continuous
homomorphism whose kernel lies in the Frattini subgroup, is a topological isomorphism as soon as it
has a continuous homomorphic section `s`: the range of `s` is closed and generates `G` together
with the Frattini subgroup, so `s` is surjective and is a two-sided inverse of `φ`.

The Frattini argument also runs relative to a pro-`p` subgroup of a profinite group which is not
itself pro-`p`. If `P` is a closed pro-`p` subgroup of `G`, a normal subgroup of `G` contained in
`Φ(P)` consists of non-generators of `G`. In particular, for a normal pro-`p` subgroup `P`, a set
generating `G` modulo `⁅P, P⁆` already generates `G`. This is how the wild inertia subgroup of the
absolute Galois group of a `p`-adic field is removed when counting generators.

## Main results

* `IsProP.eq_top_of_forall_not_le_openNormalSubgroup_index_eq`: the index-`p` detection
  criterion for closed subgroups.
* `IsProP.eq_top_of_sup_proPFrattini_eq_top`: the Frattini subgroup consists of
  non-generators.
* `IsProP.surjective_of_forall_inv_mul_mem_proPFrattini`: a continuous endomorphism congruent to
  the identity modulo the Frattini subgroup is surjective.
* `IsProP.surjective_of_surjective_comp_of_ker_le_proPFrattini`: a homomorphism with closed range
  whose composite with a Frattini cover is surjective is surjective.
* `IsProP.continuousMulEquivOfLeftInverse`: a Frattini cover with a continuous homomorphic
  section is a topological isomorphism, with the section as inverse.
* `topologicallyGenerates_iff_frattiniQuotient`: a set generates topologically if and only if
  its image generates the Frattini quotient topologically.
* `IsProP.eq_top_of_le_map_proPFrattini_of_sup_eq_top`: the relative Frattini argument, a
  normal subgroup of `G` inside the Frattini subgroup of a closed pro-`p` subgroup consists of
  non-generators of `G`.
* `IsProP.topologicalClosure_eq_top_of_sup_commutator`: a set generating `G` topologically
  together with `⁅P, P⁆`, for a normal pro-`p` subgroup `P`, generates `G` topologically.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.1) and the proof
  of (7.4.1).
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

namespace IsProP

/-- **Index-`p` detection for closed subgroups.** A closed subgroup of a profinite pro-`p`
group which is contained in no open normal subgroup of index `p` is the whole group. -/
theorem eq_top_of_forall_not_le_openNormalSubgroup_index_eq (hG : IsProP p G)
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    (h : ∀ U : OpenNormalSubgroup G, U.toSubgroup.index = p → ¬H ≤ U.toSubgroup) : H = ⊤ := by
  by_contra hHtop
  have hexists : ∃ U : OpenNormalSubgroup G, H ⊔ U.toSubgroup ≠ ⊤ := by
    by_contra! hall
    apply hHtop
    rw [H.eq_iInf_sup_openNormalSubgroup hH]
    exact top_unique (le_iInf fun U ↦ (hall U).ge)
  obtain ⟨U, hUproper⟩ := hexists
  let Q := G ⧸ U.toSubgroup
  let q : G →* Q := QuotientGroup.mk' U.toSubgroup
  let K : Subgroup Q := H.map q
  have hKproper : K ≠ ⊤ := by
    intro hK
    have hcomap := congrArg (Subgroup.comap q) hK
    simp only [K, q] at hcomap
    rw [QuotientGroup.comap_map_mk', Subgroup.comap_top] at hcomap
    exact hUproper (by simpa [sup_comm] using hcomap)
  let _ : Finite Q := Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ : Finite (Subgroup Q) :=
    Finite.of_injective (fun L : Subgroup Q ↦ (L : Set Q)) SetLike.coe_injective
  obtain ⟨M, hM, hKM⟩ := (eq_top_or_exists_le_coatom K).resolve_left hKproper
  have hQU : IsPGroup p Q := isProP_iff.mp hG U
  let _ : Group.IsNilpotent Q := hQU.isNilpotent
  let hMnormal : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom
      M (Group.normalizerCondition_of_isNilpotent (G := Q)) hM
  let _ : M.Normal := hMnormal
  have hMindex : M.index = p := hQU.index_eq_prime_of_isCoatom hM
  have hUle : U.toSubgroup ≤ M.comap q := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxq : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxq]
    exact M.one_mem
  have hVopen : IsOpen ((M.comap q : Subgroup G) : Set G) :=
    Subgroup.isOpen_mono hUle U.isOpen
  let V : OpenNormalSubgroup G :=
    { toOpenSubgroup := ⟨M.comap q, hVopen⟩
      isNormal' := hMnormal.comap q }
  have hVindex : V.toSubgroup.index = p :=
    (Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective U.toSubgroup)).trans
      hMindex
  exact h V hVindex (Subgroup.map_le_iff_le_comap.mp hKM)

/-- The pro-`p` Frattini subgroup consists of non-generators: if a closed subgroup together with
the Frattini subgroup generates the whole group, then the subgroup was already the whole group. -/
theorem eq_top_of_sup_proPFrattini_eq_top (hG : IsProP p G) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) (hsup : H ⊔ proPFrattini p G = ⊤) : H = ⊤ := by
  apply hG.eq_top_of_forall_not_le_openNormalSubgroup_index_eq hH
  intro U hU hHU
  have htop_le : (⊤ : Subgroup G) ≤ U.toSubgroup := by
    rw [← hsup]
    exact sup_le hHU (proPFrattini_le hU)
  have hUtop : U.toSubgroup = ⊤ := top_unique htop_le
  exact hp.out.ne_one <| hU.symm.trans (Subgroup.index_eq_one.mpr hUtop)

/-- **A homomorphism onto a Frattini cover is surjective.** Let `φ : G →* H` have kernel in the
Frattini subgroup `Φ(G)` of the pro-`p` group `G`. A homomorphism `s` into `G` with closed range
whose composite with `φ` is surjective is itself surjective. -/
theorem surjective_of_surjective_comp_of_ker_le_proPFrattini (hG : IsProP p G) {K H : Type*}
    [Group K] [Group H] {s : K →* G} (hs : IsClosed (s.range : Set G)) {φ : G →* H}
    (hφs : Function.Surjective (φ ∘ s)) (hker : φ.ker ≤ proPFrattini p G) :
    Function.Surjective s := by
  suffices hr : s.range = ⊤ from MonoidHom.range_eq_top.mp hr
  apply hG.eq_top_of_sup_proPFrattini_eq_top hs
  · refine top_unique fun x _ ↦ ?_
    obtain ⟨k, hk⟩ := hφs (φ x)
    have hmem : (s k)⁻¹ * x ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← Function.comp_apply (f := φ), hk, inv_mul_cancel]
    have hx := Subgroup.mul_mem_sup (MonoidHom.mem_range.mpr ⟨k, rfl⟩ : s k ∈ s.range) (hker hmem)
    rwa [mul_inv_cancel_left] at hx

/-- **An endomorphism congruent to the identity modulo the Frattini subgroup is surjective.** A
continuous endomorphism `φ` of a pro-`p` group with `g⁻¹ * φ g ∈ Φ(G)` for every `g` is
surjective. -/
theorem surjective_of_forall_inv_mul_mem_proPFrattini (hG : IsProP p G) {φ : G →* G}
    (hφ : Continuous φ) (h : ∀ g, g⁻¹ * φ g ∈ proPFrattini p G) : Function.Surjective φ :=
  hG.surjective_of_surjective_comp_of_ker_le_proPFrattini hφ.isClosedMap.isClosed_range
    (φ := QuotientGroup.mk' (proPFrattini p G))
    (fun y ↦ by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
      refine ⟨x, ?_⟩
      rw [Function.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      simpa using inv_mem (h x))
    (QuotientGroup.ker_mk' _).le

/-! ### The relative Frattini argument

A closed pro-`p` subgroup `P` of a profinite group `G` has its own Frattini subgroup `Φ(P)`. When
a normal subgroup `N` of `G` lies in `Φ(P)`, its elements are non-generators of `G` itself, even
though `G` need not be pro-`p`: if `H ⊔ N = G`, the modular law gives `P = (H ⊓ P) ⊔ N`, so
`H ⊓ P` and `Φ(P)` generate `P`, whence `P ≤ H` and `H = G`. The closure of the commutator
subgroup `⁅P, P⁆` of a closed normal pro-`p` subgroup is such an `N`. -/

/-- **The relative Frattini argument.** Let `P` be a closed pro-`p` subgroup of a profinite group
`G`, and `N` a normal subgroup of `G` contained in the pro-`p` Frattini subgroup `Φ(P)` of `P`. A
closed subgroup `H` of `G` with `H ⊔ N = G` is all of `G`. -/
theorem eq_top_of_le_map_proPFrattini_of_sup_eq_top {P : Subgroup G}
    (hPc : IsClosed (P : Set G)) (hP : IsProP p P) {N : Subgroup G} [N.Normal]
    (hN : N ≤ (proPFrattini p P).map P.subtype) {H : Subgroup G} (hH : IsClosed (H : Set G))
    (hsup : H ⊔ N = ⊤) : H = ⊤ := by
  have : CompactSpace P := isCompact_iff_compactSpace.mp hPc.isCompact
  have hNP : N ≤ P := hN.trans (Subgroup.map_subtype_le _)
  have hHP : H.subgroupOf P = ⊤ := by
    refine hP.eq_top_of_sup_proPFrattini_eq_top (hH.preimage continuous_subtype_val)
      (top_unique fun x _ ↦ ?_)
    have hx : (x : G) ∈ H ⊔ N := hsup ▸ Subgroup.mem_top _
    obtain ⟨h, hh, n, hn, hhn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨m, hm, rfl⟩ := hN hn
    -- The `H`-component `h = x * m⁻¹` of `x` lies in `P`, since `x` and `m` do.
    have hhP : h ∈ P := by
      simpa [← hhn] using P.mul_mem x.2 (P.inv_mem m.2)
    have hxm : x = ⟨h, hhP⟩ * m := Subtype.ext hhn.symm
    exact hxm ▸ Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hh) hm
  have hPH : P ≤ H := Subgroup.subgroupOf_eq_top.mp hHP
  rwa [sup_eq_left.mpr (hNP.trans hPH)] at hsup

/-- **Relative Frattini reduction along a normal pro-`p` subgroup** (NSW (3.9.1)). Let `P` be a
normal pro-`p` subgroup of a profinite group `G`. A set which topologically generates `G` together
with the commutator subgroup `⁅P, P⁆` already topologically generates `G`. -/
theorem topologicalClosure_eq_top_of_sup_commutator {P : Subgroup G} [P.Normal]
    (hP : IsProP p P) {s : Set G}
    (hs : (Subgroup.closure s ⊔ ⁅P, P⁆).topologicalClosure = ⊤) :
    (Subgroup.closure s).topologicalClosure = ⊤ := by
  -- Work with the closure `P'` of `P`, a closed normal pro-`p` subgroup, and `N = ⁅P', P'⁆‾`,
  -- which is normal in `G` and contained in `Φ(P')`.
  let P' := P.topologicalClosure
  have : P'.Normal := Subgroup.is_normal_topologicalClosure _
  have hPc : IsClosed (P' : Set G) := P.isClosed_topologicalClosure
  let H := (Subgroup.closure s).topologicalClosure
  let N := (⁅P', P'⁆ : Subgroup G).topologicalClosure
  have : N.Normal := Subgroup.is_normal_topologicalClosure _
  have hN : N ≤ (proPFrattini p P').map P'.subtype := by
    rw [← proPFrattiniStep_eq_map_proPFrattini hp.out hPc]
    exact Subgroup.topologicalClosure_minimal _ (commutator_le_proPFrattiniStep P')
      (isClosed_proPFrattiniStep P')
  -- `H ⊔ N = N * H` is the product of two compact sets, hence closed.
  have hHN : IsClosed ((H ⊔ N : Subgroup G) : Set G) := by
    rw [sup_comm, Subgroup.normal_mul]
    exact ((Subgroup.isClosed_topologicalClosure _).isCompact.mul
      (Subgroup.isClosed_topologicalClosure _).isCompact).isClosed
  refine hP.topologicalClosure.eq_top_of_le_map_proPFrattini_of_sup_eq_top hPc hN
    (Subgroup.isClosed_topologicalClosure _) (top_unique ?_)
  rw [← hs]
  have hPP : ⁅P, P⁆ ≤ N :=
    (Subgroup.commutator_mono P.le_topologicalClosure P.le_topologicalClosure).trans
      (Subgroup.le_topologicalClosure _)
  exact Subgroup.topologicalClosure_minimal _
    (sup_le_sup (Subgroup.le_topologicalClosure _) hPP) hHN

end IsProP

/-- **Burnside's basis theorem, generation form.** A set topologically generates a profinite
pro-`p` group if and only if its image topologically generates the Frattini quotient. -/
theorem topologicallyGenerates_iff_frattiniQuotient (hG : IsProP p G) (s : Set G) :
    (Subgroup.closure s).topologicalClosure = ⊤ ↔
      (Subgroup.closure ((QuotientGroup.mk' (proPFrattini p G)) '' s)).topologicalClosure = ⊤ := by
  let Φ := proPFrattini p G
  let q : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  constructor
  · intro hs
    exact topologicalClosure_closure_image_eq_top hs QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective Φ).denseRange
  · intro hs
    let K := (Subgroup.closure s).topologicalClosure
    have hKclosed : IsClosed (K : Set G) := Subgroup.isClosed_topologicalClosure _
    have hKmap_closed : IsClosed ((K.map q : Subgroup (G ⧸ Φ)) : Set (G ⧸ Φ)) := by
      rw [Subgroup.coe_map]
      exact (hKclosed.isCompact.image QuotientGroup.continuous_mk).isClosed
    have himage : q '' s ⊆ K.map q := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, Subgroup.le_topologicalClosure _ (Subgroup.subset_closure hx), rfl⟩
    have hclosure : Subgroup.closure (q '' s) ≤ K.map q :=
      (Subgroup.closure_le (K.map q)).mpr himage
    have htop_le : (⊤ : Subgroup (G ⧸ Φ)) ≤ K.map q := by
      rw [← hs]
      exact Subgroup.topologicalClosure_minimal _ hclosure hKmap_closed
    have hKmap : K.map q = ⊤ := top_unique htop_le
    have hcomap := congrArg (Subgroup.comap q) hKmap
    have hsup : K ⊔ proPFrattini p G = ⊤ := by
      simp only [K, q, Φ] at hcomap
      rw [QuotientGroup.comap_map_mk', Subgroup.comap_top] at hcomap
      simpa [sup_comm] using hcomap
    exact hG.eq_top_of_sup_proPFrattini_eq_top hKclosed hsup

/-! ### Frattini covers with a continuous homomorphic section -/

namespace IsProP

variable {H : Type v} [Group H] [TopologicalSpace H]

/-- A continuous homomorphic section of a Frattini cover of a pro-`p` group is surjective, since
its range is a closed subgroup generating the group together with the Frattini subgroup. -/
theorem surjective_of_leftInverse_of_ker_le_proPFrattini (hG : IsProP p G) {φ : G →ₜ* H}
    {s : H →ₜ* G} (hs : Function.LeftInverse φ s) (hker : φ.toMonoidHom.ker ≤ proPFrattini p G) :
    Function.Surjective s := by
  suffices h : s.toMonoidHom.range = ⊤ by simpa using MonoidHom.range_eq_top.mp h
  apply hG.eq_top_of_sup_proPFrattini_eq_top
  · rw [MonoidHom.coe_range]
    exact hs.isClosed_range φ.continuous s.continuous
  · refine top_unique fun x _ ↦ ?_
    have hmem : (s (φ x))⁻¹ * x ∈ φ.toMonoidHom.ker := by
      simp [MonoidHom.mem_ker, hs (φ x)]
    have hx := Subgroup.mul_mem_sup
      (MonoidHom.mem_range.mpr ⟨φ x, rfl⟩ : s (φ x) ∈ s.toMonoidHom.range) (hker hmem)
    rwa [mul_inv_cancel_left] at hx

/-- **A Frattini cover with a continuous homomorphic section is an isomorphism.** A continuous
homomorphism `φ : G → H` out of a pro-`p` group `G`, whose kernel lies in the Frattini subgroup
`Φ(G)` and which has a continuous homomorphic section `s`, is a topological isomorphism whose
inverse is `s`. -/
noncomputable def continuousMulEquivOfLeftInverse (hG : IsProP p G) (φ : G →ₜ* H) (s : H →ₜ* G)
    (hs : Function.LeftInverse φ s) (hker : φ.toMonoidHom.ker ≤ proPFrattini p G) : G ≃ₜ* H where
  toFun := φ
  invFun := s
  left_inv x := by
    obtain ⟨y, rfl⟩ := hG.surjective_of_leftInverse_of_ker_le_proPFrattini hs hker x
    exact congrArg s (hs y)
  right_inv := hs
  map_mul' := map_mul φ
  continuous_toFun := φ.continuous
  continuous_invFun := s.continuous

@[simp]
theorem continuousMulEquivOfLeftInverse_apply (hG : IsProP p G) (φ : G →ₜ* H) (s : H →ₜ* G)
    (hs : Function.LeftInverse φ s) (hker : φ.toMonoidHom.ker ≤ proPFrattini p G) (x : G) :
    hG.continuousMulEquivOfLeftInverse φ s hs hker x = φ x :=
  (rfl)

@[simp]
theorem continuousMulEquivOfLeftInverse_symm_apply (hG : IsProP p G) (φ : G →ₜ* H) (s : H →ₜ* G)
    (hs : Function.LeftInverse φ s) (hker : φ.toMonoidHom.ker ≤ proPFrattini p G) (y : H) :
    (hG.continuousMulEquivOfLeftInverse φ s hs hker).symm y = s y :=
  (rfl)

end IsProP

end TauCeti
