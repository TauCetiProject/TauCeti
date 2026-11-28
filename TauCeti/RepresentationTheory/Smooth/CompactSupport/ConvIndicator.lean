/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.CompactSupport
public import TauCeti.Topology.Algebra.Group.LocallyConstant.CompactSupport

/-!
# The test function `a ⋆ 1_U` of an element of the group algebra

Let `G` be a topological group, `U` a compact open subgroup of `G` and `R` a semiring. An element
`a = ∑ c_b b` of the group algebra `R[G]` gives the locally constant function with compact support
`a ⋆ 1_U = ∑ c_b 1_{bU}` on `G` (`TauCeti.convIndicator R U hU a`): the convolution of `a`, read as
a finite combination of point masses, with the indicator function of `U`. Its value at `x` is the
sum of the coefficients `c_b` over the `b` in the coset `xU`.

The map `a ↦ a ⋆ 1_U` is how elements of the group algebra are turned into test functions on a
locally profinite group such as the finite adelic points of a reductive group: it is `R`-linear,
intertwines left multiplication on `R[G]` with left translation of functions, is unchanged by right
multiplication by elements of `U`, and its image is exactly the space of test functions invariant
under right translation by `U`. On a weakly locally compact nonarchimedean group every test
function is of the form `a ⋆ 1_U` for some compact open subgroup `U`.

## Main definitions

* `TauCeti.convIndicator R U hU`: the `R`-linear map `R[G] → C_c^∞(G, R)`, `a ↦ a ⋆ 1_U`.

## Main results

* `TauCeti.coe_convIndicator`: `a ⋆ 1_U = ∑ c_b 1_{bU}`.
* `TauCeti.convIndicator_apply`: `(a ⋆ 1_U)(x)` is the sum of the coefficients of `a` over `xU`.
* `TauCeti.convIndicator_single`, `TauCeti.convIndicator_single_apply`: `(c b) ⋆ 1_U` is the
  indicator `1_{bU} • c`.
* `TauCeti.support_convIndicator_subset`: `a ⋆ 1_U` vanishes off `supp(a) U`.
* `TauCeti.convIndicator_single_mul`, `TauCeti.convIndicator_mul`: `(b a) ⋆ 1_U` is the left
  translate of `a ⋆ 1_U` by `b`, so `a ↦ a ⋆ 1_U` is a map of representations from `R[G]` to the
  translation representation `TauCeti.compactlySupportedRep`.
* `TauCeti.convIndicator_mul_single_one_of_mem`: `(a k) ⋆ 1_U = a ⋆ 1_U` for `k ∈ U`.
* `TauCeti.mem_range_convIndicator_iff`: the test functions of the form `a ⋆ 1_U` are those
  invariant under right translation by `U`.
* `TauCeti.exists_convIndicator_eq`: on a weakly locally compact nonarchimedean group, every test
  function is `a ⋆ 1_U` for some compact open subgroup `U` and some `a ∈ R[G]`.

## References

* C. J. Bushnell, G. Henniart, *The local Langlands conjecture for GL(2)*, Grundlehren der
  mathematischen Wissenschaften 335, Springer, 2006, Chapter 1, §4.
* The definition and the left translation law follow `New.convIndicator`,
  `New.convIndicator_single` and `New.convIndicator_single_mul` of the formal shorter proof
  [ShortProof], file `Lib/Adelic/TraceFormula/TestFunction.lean` of `lsernau/grh-lean`.
-/

public section

noncomputable section

open Function LocallyConstant MonoidAlgebra
open scoped Pointwise

namespace TauCeti

variable {R G : Type*} [Group G] [TopologicalSpace G]

section Semiring

variable [IsTopologicalGroup G] [Semiring R]

variable (R) in
/-- **The test function `a ⋆ 1_U`** of an element `a = ∑ c_b b` of the group algebra `R[G]`, for a
compact open subgroup `U`: the locally constant function with compact support `∑ c_b 1_{bU}`
(`TauCeti.coe_convIndicator`), whose value at `x` is the sum of the coefficients of `a` over the
coset `xU`. -/
def convIndicator (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    R[G] →ₗ[R] compactlySupported R G R :=
  Submodule.inclusion (compactlySupportedRightInvariant_le_compactlySupported _) ∘ₗ
    (compactlySupportedRightInvariantEquiv U hU).symm.toLinearMap ∘ₗ
      Finsupp.lmapDomain R R (QuotientGroup.mk : G → G ⧸ (U : Subgroup G)) ∘ₗ
        (coeffLinearEquiv R).toLinearMap

variable {U : OpenSubgroup G} {hU : IsCompact (U : Set G)}

/-- The value of `a ⋆ 1_U` at `x` is the sum of the coefficients of `a` over the coset `xU`: the
coefficient at `xU` of the image of `a` in the finitely supported functions on `G ⧸ U`. -/
theorem convIndicator_apply (a : R[G]) (x : G) :
    (convIndicator R U hU a : LocallyConstant G R) x =
      a.coeff.mapDomain (QuotientGroup.mk : G → G ⧸ (U : Subgroup G)) x := by
  simp [convIndicator]

/-- The test function `a ⋆ 1_U` is invariant under right translation by `U`. -/
theorem convIndicator_apply_mul_of_mem (a : R[G]) (x : G) {u : G} (hu : u ∈ U) :
    (convIndicator R U hU a : LocallyConstant G R) (x * u) =
      (convIndicator R U hU a : LocallyConstant G R) x := by
  rw [convIndicator_apply, convIndicator_apply, QuotientGroup.mk_mul_of_mem x hu]

/-- **`(c b) ⋆ 1_U = 1_{bU} • c`**: the test function of the multiple `c b` of a group element is
`c` on the left coset `bU` and `0` elsewhere. -/
@[simp]
theorem coe_convIndicator_single (b : G) (c : R) :
    ⇑(convIndicator R U hU (single b c) : LocallyConstant G R) =
      (b • (U : Set G)).indicator fun _ ↦ c := by
  classical
  ext x
  have h : (b : G ⧸ (U : Subgroup G)) = x ↔ x ∈ b • (U : Set G) := by
    rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, QuotientGroup.eq, SetLike.mem_coe,
      OpenSubgroup.mem_toSubgroup]
  simp only [convIndicator_apply, coeff_single, Finsupp.mapDomain_single, Finsupp.single_apply,
    Set.indicator_apply, h]

/-- The value of `(c b) ⋆ 1_U` at `x` is `c` if `b⁻¹ x ∈ U`, that is if `x ∈ bU`, and `0`
otherwise. -/
theorem convIndicator_single_apply (b : G) (c : R) (x : G) [Decidable (b⁻¹ * x ∈ U)] :
    (convIndicator R U hU (single b c) : LocallyConstant G R) x =
      if b⁻¹ * x ∈ U then c else 0 := by
  classical
  rw [coe_convIndicator_single, Set.indicator_apply]
  exact if_congr (by rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe]) rfl rfl

/-- **The support of `a ⋆ 1_U`** lies in the union `supp(a) U` of the cosets `bU` of the group
elements `b` in the support of `a`. -/
theorem support_convIndicator_subset (a : R[G]) :
    support (convIndicator R U hU a : LocallyConstant G R) ⊆
      (a.coeff.support : Set G) * (U : Set G) := by
  classical
  intro x hx
  rw [mem_support, convIndicator_apply, ← Finsupp.mem_support_iff] at hx
  -- The coset `xU` is the image of some `b` in the support of `a`, and then `x = b (b⁻¹ x)`.
  obtain ⟨b, hb, hbx⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  exact Set.mem_mul.2 ⟨b, hb, b⁻¹ * x, QuotientGroup.eq.1 hbx, mul_inv_cancel_left b x⟩

/-- **`a ⋆ 1_U = ∑ c_b 1_{bU}`**: the test function of `a` is the combination, with the coefficients
of `a`, of the indicator functions of the left cosets `bU`. -/
theorem coe_convIndicator (a : R[G]) :
    ⇑(convIndicator R U hU a : LocallyConstant G R) =
      a.coeff.sum fun b c ↦ (b • (U : Set G)).indicator fun _ ↦ c := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [map_add, Submodule.coe_add, LocallyConstant.coe_add, ha, ha', coeff_add,
      Finsupp.sum_add_index' (fun _ ↦ Set.indicator_zero' _) fun _ _ _ ↦ Set.indicator_add' _ _ _]
  | single b c =>
    rw [coe_convIndicator_single, coeff_single,
      Finsupp.sum_single_index (Set.indicator_zero' _)]

/-- **`(c b) ⋆ 1_U` is an indicator.** In a Hausdorff group, the test function of `c b` is the
indicator `1_{bU} • c` of the compact open set `bU`. -/
theorem convIndicator_single [T2Space G] (b : G) (c : R) :
    (convIndicator R U hU (single b c) : LocallyConstant G R) =
      compactOpenIndicator (b • U.toCompactOpens hU) c :=
  LocallyConstant.coe_injective <| by
    rw [coe_convIndicator_single, coe_compactOpenIndicator, TopologicalSpace.CompactOpens.coe_smul,
      OpenSubgroup.coe_toCompactOpens]

/-- **`1 ⋆ 1_U = 1_U`**: the test function of the unit of the group algebra is the indicator
function of `U`. -/
@[simp]
theorem coe_convIndicator_one :
    ⇑(convIndicator R U hU 1 : LocallyConstant G R) = (U : Set G).indicator fun _ ↦ 1 := by
  rw [one_def, coe_convIndicator_single, one_smul]

/-- **Left multiplication is left translation.** The test function of `(c g) a` is `c` times the
left translate of `a ⋆ 1_U` by `g`, the function `x ↦ (a ⋆ 1_U)(g⁻¹ x)`. -/
theorem convIndicator_single_mul (g : G) (c : R) (a : R[G]) :
    convIndicator R U hU (single g c * a) =
      c • compactlySupportedRep R G G R g (convIndicator R U hU a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' => rw [mul_add, map_add, ha, ha', map_add, map_add, smul_add]
  | single b c' =>
    classical
    ext x
    -- Both sides are `c c'` at the points of `gbU` and `0` elsewhere.
    simp only [single_mul_single, Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply,
      compactlySupportedRep_apply_coe, coe_convIndicator_single, Set.indicator_apply,
      Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, mul_inv_rev, mul_assoc, mul_ite, mul_zero]

/-- The value of the test function of `(c g) a` at `x` is `c (a ⋆ 1_U)(g⁻¹ x)`. -/
@[simp]
theorem convIndicator_single_mul_apply (g : G) (c : R) (a : R[G]) (x : G) :
    (convIndicator R U hU (single g c * a) : LocallyConstant G R) x =
      c * (convIndicator R U hU a : LocallyConstant G R) (g⁻¹ * x) := by
  rw [convIndicator_single_mul, Submodule.coe_smul, LocallyConstant.coe_smul, Pi.smul_apply,
    compactlySupportedRep_apply_coe, smul_eq_mul, smul_eq_mul]

/-- **Right multiplication by elements of `U` does not change the test function**: for `k ∈ U`,
`(a k) ⋆ 1_U = a ⋆ 1_U`, as `bkU = bU`. -/
theorem convIndicator_mul_single_one_of_mem (a : R[G]) {k : G} (hk : k ∈ U) :
    convIndicator R U hU (a * single k 1) = convIndicator R U hU a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' => rw [add_mul, map_add, ha, ha', map_add]
  | single b c =>
    refine Subtype.ext <| LocallyConstant.coe_injective ?_
    rw [single_mul_single, mul_one, coe_convIndicator_single, coe_convIndicator_single,
      ← smul_smul, smul_coe_set hk]

/-- **The image of `a ↦ a ⋆ 1_U`** is the space of test functions invariant under right
translation by `U`. -/
theorem mem_range_convIndicator_iff {f : compactlySupported R G R} :
    f ∈ LinearMap.range (convIndicator R U hU) ↔
      ∀ u ∈ U, ∀ x, (f : LocallyConstant G R) (x * u) = (f : LocallyConstant G R) x := by
  refine ⟨?_, fun hf ↦ ?_⟩
  · rintro ⟨a, rfl⟩ u hu x
    exact convIndicator_apply_mul_of_mem a x hu
  · -- `f` is the test function of a lift to `R[G]` of its finitely supported function on `G ⧸ U`.
    let f' : compactlySupportedRightInvariant R R (U : Subgroup G) :=
      ⟨f, mem_compactlySupportedRightInvariant.2 ⟨mem_compactlySupported.1 f.property, hf⟩⟩
    obtain ⟨a, ha⟩ := Finsupp.mapDomain_surjective QuotientGroup.mk_surjective
      (compactlySupportedRightInvariantEquiv U hU f')
    refine ⟨ofCoeff a, compactlySupported.ext fun x ↦ ?_⟩
    rw [convIndicator_apply, ha, compactlySupportedRightInvariantEquiv_apply_mk]

end Semiring

section CommSemiring

variable [IsTopologicalGroup G] [CommSemiring R] {U : OpenSubgroup G} {hU : IsCompact (U : Set G)}

/-- **`a ↦ a ⋆ 1_U` is a map of representations**: the test function of a product `b a` in the
group algebra is the image of `a ⋆ 1_U` under `b`, acting through the translation representation
`(g • f)(x) = f(g⁻¹ x)`. -/
theorem convIndicator_mul (b a : R[G]) :
    convIndicator R U hU (b * a) =
      (compactlySupportedRep R G G R).asAlgebraHom b (convIndicator R U hU a) := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b b' hb hb' => rw [add_mul, map_add, hb, hb', map_add, LinearMap.add_apply]
  | single g c =>
    rw [convIndicator_single_mul, Representation.asAlgebraHom_single, LinearMap.smul_apply]

end CommSemiring

/-- **Every test function is some `a ⋆ 1_U`.** On a weakly locally compact nonarchimedean group,
in particular on a locally profinite group, every locally constant function with compact support
is the test function `a ⋆ 1_U` of an element `a` of the group algebra, for some compact open
subgroup `U`. -/
theorem exists_convIndicator_eq [Semiring R] [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (f : compactlySupported R G R) :
    ∃ (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) (a : R[G]), convIndicator R U hU a = f := by
  obtain ⟨U, hU, hf⟩ :=
    exists_isCompact_openSubgroup_forall_mul_eq (mem_compactlySupported.1 f.property)
  obtain ⟨a, ha⟩ := mem_range_convIndicator_iff.2 fun u hu x ↦ (hf u hu x).2
  exact ⟨U, hU, a, ha⟩

end TauCeti
