/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Orthogonality
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Reciprocity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Comparison

/-!
# Global reciprocity and the dual-Selmer obstruction pairing for an isogeny

Let `φ : E₁ → E₂` be an isogeny of elliptic curves over a number field `K`, with embeddings of
separable closures `τ v` at each finite place `v` and `τ' w` at each infinite place `w`. The global
`φ`-Selmer group imposing the local Kummer conditions at all places (finite and infinite) is the
intersection `φ.selmerGroup τ ⊓ φ.selmerGroup τ'`, and likewise for the dual isogeny `φ̂`.

Combining local orthogonality of the `φ`- and `φ̂`-Selmer conditions
(`TauCeti.Isogeny.kerWeilBrauerPairing_eq_zero_of_mem_ker` and
`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_ker`) with global Brauer reciprocity for
the isogeny Weil cup product
(`TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero`)
constrains how global classes in `H¹(K, E₁[φ])` can fail the local `φ`-Selmer conditions when
tested against the dual Selmer group:

* at every place (finite or infinite) where `a ∈ H¹(K, E₁[φ])` satisfies the local `φ`-Selmer
  condition, its local pairing with every class in the corresponding dual Selmer group vanishes —
  in `H²(K_v, μ_{deg φ})`, in `Br K_v`, under the nonarchimedean local Tate pairing, and under the
  archimedean invariant map;
* consequently, whenever `a ∈ φ.selmerGroup τ'` and `b ∈ φ.dual.selmerGroup τ'` satisfy the
  archimedean Selmer conditions, the archimedean terms drop out of the global reciprocity law and
  the finitely supported sum of their `ℚ/ℤ`-valued local Tate pairings over all finite places
  vanishes;
* if `a ∈ φ.selmerGroup τ'` also satisfies the `φ`-Selmer condition outside a finite set `S` of
  finite places, the sum over `S` of its `ℚ/ℤ`-valued local Tate pairings with any
  `b ∈ φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ'` is zero; in particular, if `a` satisfies the
  `φ`-Selmer condition at every place except possibly one finite place `v₀`, its `ℤ/(deg φ)`-valued
  local Tate pairing with the global dual Selmer group vanishes at `v₀` as well;
* summing the local Tate obstruction pairings (`TauCeti.Isogeny.localSelmerObstructionPairing`)
  over `S` defines the bilinear Cassels / Poitou–Tate obstruction pairing
  `(∏_{v ∈ S} H¹(K_v, E₁[φ]) ⧸ H¹_φ(K_v)) × Sel_φ̂(E₂/K) → ℚ/ℤ`, which annihilates the localization
  image of any relaxed global Selmer group whose finite-place conditions are contained in those of
  `Sel_φ` outside `S`.

This supplies the global-duality half of the Poitou–Tate / Cassels comparison sequence

```text
0 ⟶ Sel_φ(E₁/K) ⟶ Sel_A(E₁/K) ⟶ ∏_{v ∈ S} H¹(K_v, E₁[φ]) ⧸ H¹_φ(K_v) ⟶ Hom(Sel_φ̂(E₂/K), ℚ/ℤ)
```

used in Cassels' proof of the isogeny invariance of the Birch–Swinnerton-Dyer quotient.

## Main definitions

* `TauCeti.Isogeny.dualSelmerLocalization`: localization of `φ.dual.selmerGroup` into the local
  `φ̂`-Selmer condition for `(φ.baseChange (L i)).dual`.
* `TauCeti.Isogeny.globalObstructionMap`: localization of `H¹(K, E₁[φ])` into the finite product
  `∏_{i ∈ S} H¹(L_i, E₁[φ]) ⧸ H¹_φ(L_i)` of local quotients modulo the `φ`-Selmer conditions.
* `TauCeti.Isogeny.localSelmerObstructionPairing`: the local Tate obstruction pairing at a finite
  place between `H¹(K_v, E₁[φ]) ⧸ H¹_φ(K_v)` and `φ.dual.selmerGroup τ`.
* `TauCeti.Isogeny.selmerObstructionPairing`: the bilinear obstruction pairing on
  `(∏_{v ∈ S} H¹(K_v, E₁[φ]) ⧸ H¹_φ(K_v)) × (φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ')` with
  values in `ℚ/ℤ`.

## Main results

* `TauCeti.Isogeny.finsum_toRatAddCircle_localTateKerWeilPairing_eq_zero`: finite-place reciprocity
  when `a` and `b` satisfy the archimedean `φ`- and `φ̂`-Selmer conditions.
* `TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero` and
  `TauCeti.Isogeny.localTateKerWeilPairing_kerRes_eq_zero_of_forall_ne`: finite-set and
  single-place reciprocity against the global dual Selmer group.
* `TauCeti.Isogeny.exact_inclusion_globalObstructionMap` and
  `TauCeti.Isogeny.selmerObstructionPairing_comp_globalObstructionMap_eq_zero`: exactness at the
  relaxed Selmer group and vanishing of the composite into `Hom(Sel_φ̂(E₂/K), ℚ/ℤ)`.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199, §3.
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §4 and Theorem 6.13.
-/

public section

noncomputable section

open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open IsDedekindDomain NumberField

namespace TauCeti.Isogeny

open Hom (ofIsogeny)

/-! ### Local orthogonality and comparison maps over an arbitrary field -/

section Field

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  {ι : Type*} {L : ι → Type*} [∀ i, Field (L i)] [∀ i, Algebra K (L i)]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ i, SeparableClosure K →ₐ[K] SeparableClosure (L i))

/-- `φ.selmerGroup τ` is the Selmer group of `φ.selmerStructure τ`. -/
theorem selmerGroup_eq_selmerStructure_selmerGroup :
    φ.selmerGroup τ = (φ.selmerStructure τ).selmerGroup := by
  ext c
  simp only [mem_selmerGroup_iff, mem_shafarevichTateGroup_iff, pointRes_kerCoeffIncl,
    SelmerStructure.mem_selmerGroup_iff, selmerStructure_localization,
    selmerStructure_localCondition, AddMonoidHom.mem_ker]

/-- Restricting a class in `Sel_φ` along `kerRes (τ i)` lands in the `i`-th local condition of
`selmerStructure φ τ`. -/
theorem kerRes_mem_localCondition_of_mem_selmerGroup
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (ha : a ∈ φ.selmerGroup τ) (i : ι) :
    φ.kerRes (τ i) a ∈ (φ.selmerStructure τ).localCondition i := by
  have ha' : a ∈ (φ.selmerStructure τ).selmerGroup := by
    rwa [← φ.selmerGroup_eq_selmerStructure_selmerGroup τ]
  have hmem := (φ.selmerStructure τ).mem_selmerGroup_iff.1 ha' i
  rwa [selmerStructure_localization] at hmem

/-- Enlarging every local condition of `selmerStructure φ τ` enlarges `Sel_φ`. -/
theorem selmerGroup_le_withLocalConditions
    (A : ∀ i,
      AddSubgroup (H1 (AbsoluteGaloisGroup (L i)) (ofIsogeny (φ.baseChange (L i))).KerCoeff))
    (hle : ∀ i, (φ.selmerStructure τ).localCondition i ≤ A i) :
    φ.selmerGroup τ ≤ ((φ.selmerStructure τ).withLocalConditions A).selmerGroup := by
  rw [φ.selmerGroup_eq_selmerStructure_selmerGroup τ]
  exact (φ.selmerStructure τ).selmerGroup_le _
    (fun _ ↦ by rw [SelmerStructure.withLocalConditions_localization])
    fun i ↦ by rw [SelmerStructure.withLocalConditions_localCondition]; exact hle i

/-- **Global localization into the local obstruction quotients over `S`**: sends `a ∈ H¹(K, E₁[φ])`
to the tuple of its localizations modulo the `φ`-Selmer local conditions at `i ∈ S`. -/
def globalObstructionMap (S : Finset ι) :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      ∀ i : S,
        H1 (AbsoluteGaloisGroup (L i.1))
            (ofIsogeny (φ.baseChange (L i.1))).KerCoeff ⧸
          (φ.selmerStructure τ).localCondition i.1 :=
  AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk' ((φ.selmerStructure τ).localCondition i.1)).comp
      (φ.kerRes (τ i.1))

@[simp]
theorem globalObstructionMap_apply (S : Finset ι)
    (a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) (i : S) :
    φ.globalObstructionMap τ S a i = QuotientAddGroup.mk (φ.kerRes (τ i.1) a) :=
  (rfl)

/-- **Exactness at the relaxed Selmer group in the Cassels / Poitou–Tate comparison sequence**:
when `A` contains the `φ`-Selmer conditions of `τ` everywhere and is contained in them outside `S`,
the kernel of `globalObstructionMap` on
`((φ.selmerStructure τ).withLocalConditions A).selmerGroup ⊓ H` (for any auxiliary subgroup `H`,
such as the archimedean Selmer condition) is `(φ.selmerGroup τ) ⊓ H`. -/
theorem exact_inclusion_globalObstructionMap (S : Finset ι)
    (A : ∀ i,
      AddSubgroup (H1 (AbsoluteGaloisGroup (L i)) (ofIsogeny (φ.baseChange (L i))).KerCoeff))
    (H : AddSubgroup (H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff))
    (hle : ∀ i, (φ.selmerStructure τ).localCondition i ≤ A i)
    (hS : ∀ i ∉ S, A i ≤ (φ.selmerStructure τ).localCondition i) :
    Function.Exact
      (AddSubgroup.inclusion (inf_le_inf_right H (φ.selmerGroup_le_withLocalConditions τ A hle)))
      ((φ.globalObstructionMap τ S).comp
        (((φ.selmerStructure τ).withLocalConditions A).selmerGroup ⊓ H).subtype) := by
  intro c
  simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, funext_iff,
    globalObstructionMap_apply, Pi.zero_apply, QuotientAddGroup.eq_zero_iff, Subtype.forall]
  refine ⟨fun hc ↦ ?_, fun ⟨x, hx⟩ i _ ↦ ?_⟩
  · refine ⟨⟨c.1, AddSubgroup.mem_inf.2 ⟨?_, c.2.2⟩⟩, rfl⟩
    rw [φ.selmerGroup_eq_selmerStructure_selmerGroup τ, SelmerStructure.mem_selmerGroup_iff]
    intro i
    by_cases hi : i ∈ S
    · rw [selmerStructure_localization]
      exact hc i hi
    · have hmem :=
        ((φ.selmerStructure τ).withLocalConditions A).localization_mem ⟨c.1, c.2.1⟩ i
      rw [SelmerStructure.withLocalConditions_localization,
        SelmerStructure.withLocalConditions_localCondition] at hmem
      exact hS i hi hmem
  · exact hx ▸ φ.kerRes_mem_localCondition_of_mem_selmerGroup τ x.2.1 i

/-- Restricting a class in `Sel_φ̂` along `dualKerRes (τ i)` lands in the local Selmer kernel for
`(φ.baseChange (L i)).dual`. -/
theorem dualKerRes_mem_ker_of_mem_selmerGroup
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (hb : b ∈ φ.dual.selmerGroup τ) (i : ι) :
    φ.dualKerRes (τ i) b ∈
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (L i)).dual).kerCoeffIncl
        continuous_of_discreteTopology).ker := by
  have hb' := (W₂.mem_shafarevichTateGroup_iff τ).1 ((φ.dual.mem_selmerGroup_iff τ).1 hb) i
  rw [AddMonoidHom.mem_ker]
  exact (φ.pointRes_kerCoeffIncl_dual (L := L i) (τ i) b).symm.trans hb'

/-- **Localization of `Sel_φ̂` into the `i`-th local dual-Selmer condition**, typed directly in the
kernel carrier of `(φ.baseChange (L i)).dual` consumed by the local Weil pairings. -/
def dualSelmerLocalization (i : ι) :
    φ.dual.selmerGroup τ →+
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (L i)).dual).kerCoeffIncl
        continuous_of_discreteTopology).ker :=
  ((φ.dualKerRes (τ i)).comp (φ.dual.selmerGroup τ).subtype).codRestrict _ fun b ↦
    φ.dualKerRes_mem_ker_of_mem_selmerGroup τ b.2 i

@[simp]
theorem coe_dualSelmerLocalization (i : ι) (b : φ.dual.selmerGroup τ) :
    (φ.dualSelmerLocalization τ i b :
      H1 (AbsoluteGaloisGroup (L i)) (ofIsogeny (φ.baseChange (L i)).dual).KerCoeff) =
      φ.dualKerRes (τ i) b :=
  (rfl)

/-- At any index `i` where `a ∈ H¹(K, E₁[φ])` satisfies the `φ`-Selmer local condition, its
restricted isogeny Weil cup product with any class in `Sel_φ̂` vanishes in `H²(L i, μ_{deg φ})`. -/
theorem kerH1WeilPairing_kerRes_eq_zero_of_mem_localCondition (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} {i : ι}
    (ha : φ.kerRes (τ i) a ∈ (φ.selmerStructure τ).localCondition i)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    (φ.baseChange (L i)).kerH1WeilPairing (φ.isUnit_degree_baseChange (L i) hn)
      (φ.kerRes (τ i) a) (φ.dualKerRes (τ i) b) = 0 := by
  rw [selmerStructure_localCondition] at ha
  exact (φ.baseChange (L i)).kerH1WeilPairing_eq_zero_of_mem_ker _ ha
    (φ.dualKerRes_mem_ker_of_mem_selmerGroup τ hb i)

/-- At any index `i` where `a ∈ H¹(K, E₁[φ])` satisfies the `φ`-Selmer local condition, its
restricted Brauer-valued isogeny Weil pairing with any class in `Sel_φ̂` vanishes in `Br (L i)`. -/
theorem kerWeilBrauerPairing_kerRes_eq_zero_of_mem_localCondition (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff} {i : ι}
    (ha : φ.kerRes (τ i) a ∈ (φ.selmerStructure τ).localCondition i)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    (φ.baseChange (L i)).kerWeilBrauerPairing (φ.isUnit_degree_baseChange (L i) hn)
      (φ.kerRes (τ i) a) (φ.dualKerRes (τ i) b) = 0 := by
  rw [selmerStructure_localCondition] at ha
  exact (φ.baseChange (L i)).kerWeilBrauerPairing_eq_zero_of_mem_ker _ ha
    (φ.dualKerRes_mem_ker_of_mem_selmerGroup τ hb i)

/-- For `a ∈ Sel_φ` and `b ∈ Sel_φ̂`, the restricted Brauer-valued isogeny Weil pairing vanishes at
every index `i`. -/
theorem kerWeilBrauerPairing_kerRes_eq_zero_of_mem_selmerGroup (hn : IsUnit (φ.degree : K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ φ.selmerGroup τ) (hb : b ∈ φ.dual.selmerGroup τ) (i : ι) :
    (φ.baseChange (L i)).kerWeilBrauerPairing (φ.isUnit_degree_baseChange (L i) hn)
      (φ.kerRes (τ i) a) (φ.dualKerRes (τ i) b) = 0 :=
  φ.kerWeilBrauerPairing_kerRes_eq_zero_of_mem_localCondition τ hn
    (φ.kerRes_mem_localCondition_of_mem_selmerGroup τ ha i) hb

end Field

/-! ### Global reciprocity against `Sel_φ̂` over a number field -/

section NumberField

variable {K : Type} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ v : HeightOneSpectrum (𝓞 K),
    SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
  (τ' : ∀ w : InfinitePlace K, SeparableClosure K →ₐ[K] SeparableClosure w.Completion)

/-- At a finite place `v` where `a ∈ H¹(K, E₁[φ])` satisfies the `φ`-Selmer local condition, its
local Tate pairing with any `b ∈ φ.dual.selmerGroup τ` vanishes, including at places dividing
`deg φ`. -/
theorem localTateKerWeilPairing_kerRes_eq_zero_of_mem_localCondition
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    {v : HeightOneSpectrum (𝓞 K)}
    (ha : φ.kerRes (τ v) a ∈ (φ.selmerStructure τ).localCondition v)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    (φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
      (φ.isUnit_degree_baseChange (v.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)
      (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b) = 0 := by
  rw [φ.selmerStructure_localCondition τ v] at ha
  exact (φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing_eq_zero_of_mem_ker _ ha
    (φ.dualKerRes_mem_ker_of_mem_selmerGroup τ hb v)

omit [NumberField K] in
/-- At an infinite place `w`, if the localizations of `a` and `b` lie in the local `φ`- and
`φ̂`-Selmer kernels over `K_w`, the archimedean Brauer invariant of their Weil pairing vanishes. -/
theorem infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_ker
    {w : InfinitePlace K} {a : H1 (AbsoluteGaloisGroup w.Completion)
      (ofIsogeny (φ.baseChange w.Completion)).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup w.Completion)
      (ofIsogeny (φ.baseChange w.Completion).dual).KerCoeff}
    (hn : IsUnit ((φ.baseChange w.Completion).degree : w.Completion))
    (ha : a ∈ (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion)).kerCoeffIncl
      continuous_of_discreteTopology).ker)
    (hb : b ∈ (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion).dual).kerCoeffIncl
      continuous_of_discreteTopology).ker) :
    infiniteInvMap w ((φ.baseChange w.Completion).kerWeilBrauerPairing hn a b) = 0 :=
  (congrArg (infiniteInvMap w)
    ((φ.baseChange w.Completion).kerWeilBrauerPairing_eq_zero_of_mem_ker hn ha hb)).trans
    (map_zero _)

/-- When `a ∈ φ.selmerGroup τ'` and `b ∈ φ.dual.selmerGroup τ'` satisfy the archimedean Selmer
conditions, the archimedean Brauer invariant of their Weil pairing vanishes at every infinite
place `w`. -/
theorem infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_selmerGroup
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha' : a ∈ φ.selmerGroup τ') (hb' : b ∈ φ.dual.selmerGroup τ') (w : InfinitePlace K) :
    infiniteInvMap w
      ((φ.baseChange w.Completion).kerWeilBrauerPairing
        (φ.isUnit_degree_baseChange w.Completion (NeZero.ne (φ.degree : K)).isUnit)
        (φ.kerRes (τ' w) a) (φ.dualKerRes (τ' w) b)) = 0 :=
  (congrArg (infiniteInvMap w)
    (φ.kerWeilBrauerPairing_kerRes_eq_zero_of_mem_selmerGroup τ'
      (NeZero.ne (φ.degree : K)).isUnit ha' hb' w)).trans
    (map_zero _)

/-- **Finite-place reciprocity under archimedean Selmer conditions.** If `a ∈ φ.selmerGroup τ'` and
`b ∈ φ.dual.selmerGroup τ'` satisfy the `φ`- and `φ̂`-Selmer conditions at every infinite place of
`K`, the finitely supported sum over all finite places of their `ℚ/ℤ`-valued local Tate pairings is
zero. -/
theorem finsum_toRatAddCircle_localTateKerWeilPairing_eq_zero
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha' : a ∈ φ.selmerGroup τ') (hb' : b ∈ φ.dual.selmerGroup τ') :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K),
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))) = 0 := by
  have hsum := φ.finsum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteInvMap_eq_zero
    (NeZero.ne (φ.degree : K)).isUnit a b τ τ'
  have hzero :
      (∑ w : InfinitePlace K, infiniteInvMap w
        ((φ.baseChange w.Completion).kerWeilBrauerPairing
          (φ.isUnit_degree_baseChange w.Completion (NeZero.ne (φ.degree : K)).isUnit)
          (φ.kerRes (τ' w) a) (φ.dualKerRes (τ' w) b))) = 0 :=
    Finset.sum_eq_zero fun w _ ↦
      φ.infiniteInvMap_kerWeilBrauerPairing_eq_zero_of_mem_selmerGroup τ' ha' hb' w
  exact (add_zero _).symm.trans ((congrArg (_ + ·) hzero.symm).trans hsum)

/-- **Finite-set reciprocity against `Sel_φ̂(E₂/K)`.** If `a ∈ φ.selmerGroup τ'` satisfies the
`φ`-Selmer condition at every infinite place and at every finite place outside `S`, then the sum
over `S` of its `ℚ/ℤ`-valued local Tate pairings with any
`b ∈ φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ'` vanishes. -/
theorem sum_toRatAddCircle_localTateKerWeilPairing_eq_zero
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha' : a ∈ φ.selmerGroup τ')
    (hS : ∀ v ∉ S, φ.kerRes (τ v) a ∈ (φ.selmerStructure τ).localCondition v)
    (hb : b ∈ φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ') :
    (∑ v ∈ S,
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b))) = 0 := by
  refine (finsum_eq_sum_of_support_subset _ (s := S) fun v hv ↦ ?_).symm.trans
    (φ.finsum_toRatAddCircle_localTateKerWeilPairing_eq_zero τ τ' ha' hb.2)
  rw [Function.mem_support] at hv
  by_contra hvS
  exact hv <|
    (congrArg (ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree)
      (φ.localTateKerWeilPairing_kerRes_eq_zero_of_mem_localCondition τ (hS v hvS) hb.1)).trans
      (map_zero _)

/-- **Single-place reciprocity against `Sel_φ̂(E₂/K)`.** If `a ∈ φ.selmerGroup τ'` satisfies the
`φ`-Selmer condition at every infinite place and at every finite place `v ≠ v₀`, then its local Tate
pairing with every `b ∈ φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ'` vanishes at `v₀` as well. -/
theorem localTateKerWeilPairing_kerRes_eq_zero_of_forall_ne
    {v₀ : HeightOneSpectrum (𝓞 K)}
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha' : a ∈ φ.selmerGroup τ')
    (hne : ∀ v ≠ v₀, φ.kerRes (τ v) a ∈ (φ.selmerStructure τ).localCondition v)
    (hb : b ∈ φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ') :
    (φ.baseChange (v₀.adicCompletion K)).localTateKerWeilPairing
      (φ.isUnit_degree_baseChange (v₀.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)
      (φ.kerRes (τ v₀) a) (φ.dualKerRes (τ v₀) b) = 0 := by
  classical
  have hsum := φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero τ τ' (S := {v₀}) ha'
    (fun v hv ↦ hne v fun h ↦ hv (Finset.mem_singleton.2 h)) hb
  rw [Finset.sum_singleton] at hsum
  exact (ZMod.toRatAddCircle_eq_zero _).1 hsum

/-! ### The Cassels / Poitou–Tate obstruction pairing on relaxed Selmer groups -/

/-- **The local Tate obstruction pairing at a finite place `v`** for `selmerStructure φ τ`: pairs
the local quotient `H¹(K_v, E₁[φ]) ⧸ H¹_φ(K_v)` with `φ.dual.selmerGroup τ` into `ℤ/(deg φ)`. -/
def localSelmerObstructionPairing (v : HeightOneSpectrum (𝓞 K)) :
    (H1 (AbsoluteGaloisGroup (v.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff ⧸
      (φ.selmerStructure τ).localCondition v) →+
      φ.dual.selmerGroup τ →+ ZMod (φ.baseChange (v.adicCompletion K)).degree :=
  ((((φ.baseChange (v.adicCompletion K)).localTateObstructionPairing
      (φ.isUnit_degree_baseChange (v.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)).comp
    (QuotientAddGroup.map ((φ.selmerStructure τ).localCondition v)
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
        continuous_of_discreteTopology).ker
      (AddMonoidHom.id _)
      fun _ hx ↦ (φ.selmerStructure_localCondition τ v) ▸ hx)).flip.comp
    (φ.dualSelmerLocalization τ v)).flip

@[simp]
theorem localSelmerObstructionPairing_mk (v : HeightOneSpectrum (𝓞 K))
    (a : H1 (AbsoluteGaloisGroup (v.adicCompletion K))
      (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff)
    (b : φ.dual.selmerGroup τ) :
    φ.localSelmerObstructionPairing τ v (QuotientAddGroup.mk a) b =
      (φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
        (φ.isUnit_degree_baseChange (v.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)
        a (φ.dualKerRes (τ v) b) := by
  simp [localSelmerObstructionPairing]

/-- **The Cassels / Poitou–Tate obstruction pairing** over a finite set `S` of finite places: pairs
a tuple of local quotient classes in `∏_{v ∈ S} H¹(K_v, E₁[φ]) ⧸ H¹_φ(K_v)` with a global dual
Selmer class `b ∈ φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ'` by summing the `ℚ/ℤ`-valued local
Tate obstruction pairings over `S`. -/
def selmerObstructionPairing (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ v : S,
      H1 (AbsoluteGaloisGroup (v.1.adicCompletion K))
          (ofIsogeny (φ.baseChange (v.1.adicCompletion K))).KerCoeff ⧸
        (φ.selmerStructure τ).localCondition v.1) →+
      ↥(φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ') →+ AddCircle (1 : ℚ) where
  toFun x :=
    { toFun := fun b ↦
        ∑ v : S,
          ZMod.toRatAddCircle (φ.baseChange (v.1.adicCompletion K)).degree
            (φ.localSelmerObstructionPairing τ v.1 (x v) (AddSubgroup.inclusion inf_le_left b))
      map_zero' := by simp
      map_add' := fun _ _ ↦ by simp [map_add, Finset.sum_add_distrib] }
  map_zero' := by
    refine AddMonoidHom.ext fun _ ↦ ?_
    simp
  map_add' _ _ := by
    refine AddMonoidHom.ext fun _ ↦ ?_
    simp [Pi.add_apply, map_add, Finset.sum_add_distrib]

@[simp]
theorem selmerObstructionPairing_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : ∀ v : S,
      H1 (AbsoluteGaloisGroup (v.1.adicCompletion K))
          (ofIsogeny (φ.baseChange (v.1.adicCompletion K))).KerCoeff ⧸
        (φ.selmerStructure τ).localCondition v.1)
    (b : ↥(φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ')) :
    φ.selmerObstructionPairing τ τ' S x b =
      ∑ v : S,
        ZMod.toRatAddCircle (φ.baseChange (v.1.adicCompletion K)).degree
          (φ.localSelmerObstructionPairing τ v.1 (x v) (AddSubgroup.inclusion inf_le_left b)) :=
  (rfl)

/-- **Global classes unramified outside `S` are orthogonal to `Sel_φ̂(E₂/K)` under the obstruction
pairing.** -/
theorem selmerObstructionPairing_globalObstructionMap_eq_zero
    {S : Finset (HeightOneSpectrum (𝓞 K))}
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (ha' : a ∈ φ.selmerGroup τ')
    (hS : ∀ v ∉ S, φ.kerRes (τ v) a ∈ (φ.selmerStructure τ).localCondition v)
    (b : ↥(φ.dual.selmerGroup τ ⊓ φ.dual.selmerGroup τ')) :
    φ.selmerObstructionPairing τ τ' S (φ.globalObstructionMap τ S a) b = 0 := by
  rw [selmerObstructionPairing_apply]
  have hcongr :
      (∑ v : S,
        ZMod.toRatAddCircle (φ.baseChange (v.1.adicCompletion K)).degree
          (φ.localSelmerObstructionPairing τ v.1
            (φ.globalObstructionMap τ S a v) (AddSubgroup.inclusion inf_le_left b))) =
        ∑ v : S,
          ZMod.toRatAddCircle (φ.baseChange (v.1.adicCompletion K)).degree
            ((φ.baseChange (v.1.adicCompletion K)).localTateKerWeilPairing
              (φ.isUnit_degree_baseChange (v.1.adicCompletion K)
                (NeZero.ne (φ.degree : K)).isUnit)
              (φ.kerRes (τ v.1) a) (φ.dualKerRes (τ v.1) b.1)) :=
    Finset.sum_congr rfl fun v _ ↦
      congrArg (ZMod.toRatAddCircle (φ.baseChange (v.1.adicCompletion K)).degree) <|
        (congrArg
          (fun q ↦ φ.localSelmerObstructionPairing τ v.1 q (AddSubgroup.inclusion inf_le_left b))
          (φ.globalObstructionMap_apply τ S a v)).trans
          (φ.localSelmerObstructionPairing_mk τ v.1
            (φ.kerRes (τ v.1) a) (AddSubgroup.inclusion inf_le_left b))
  exact hcongr.trans <|
    (S.sum_coe_sort fun v ↦
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K) (NeZero.ne (φ.degree : K)).isUnit)
          (φ.kerRes (τ v) a) (φ.dualKerRes (τ v) b.1))).trans
      (φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero τ τ' ha' hS b.2)

/-- **The localization image of a relaxed global Selmer group is annihilated by `Sel_φ̂(E₂/K)`**
whenever `A` is contained in the finite-place `φ`-Selmer local conditions outside `S`. -/
theorem selmerObstructionPairing_comp_globalObstructionMap_eq_zero
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : ∀ v : HeightOneSpectrum (𝓞 K),
      AddSubgroup (H1 (AbsoluteGaloisGroup (v.adicCompletion K))
        (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff))
    (hS : ∀ v ∉ S, A v ≤ (φ.selmerStructure τ).localCondition v) :
    (φ.selmerObstructionPairing τ τ' S).comp
      ((φ.globalObstructionMap τ S).comp
        (((φ.selmerStructure τ).withLocalConditions A).selmerGroup ⊓
          φ.selmerGroup τ').subtype) = 0 := by
  refine AddMonoidHom.ext fun c ↦ AddMonoidHom.ext fun b ↦ ?_
  simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, AddMonoidHom.zero_apply]
  refine φ.selmerObstructionPairing_globalObstructionMap_eq_zero τ τ' c.2.2 (fun v hv ↦ ?_) b
  have hmem :=
    ((φ.selmerStructure τ).withLocalConditions A).localization_mem ⟨c.1, c.2.1⟩ v
  rw [SelmerStructure.withLocalConditions_localization,
    SelmerStructure.withLocalConditions_localCondition, selmerStructure_localization] at hmem
  exact hS v hv hmem

end NumberField

end TauCeti.Isogeny
