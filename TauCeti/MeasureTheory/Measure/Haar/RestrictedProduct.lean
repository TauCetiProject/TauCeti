/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import TauCeti.MeasureTheory.Constructions.BorelSpace.RestrictedProduct
public import TauCeti.MeasureTheory.Measure.Haar.InfinitePi
public import TauCeti.Topology.Algebra.RestrictedProduct.Congr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import TauCeti.MeasureTheory.Group.Arithmetic

/-!
# Convergent restricted products of local Haar measures

Let `(G i)` be a countable family of second-countable locally compact topological groups equipped
with open subgroups `B i` that are compact outside a finite set of indices, together with left Haar
measures `μ i` on `G i`.

We construct left Haar measures on the cofinite restricted product `Πʳ i, [G i, B i]` in two
increasingly general regimes:

1. **Normalized restricted Haar product** (`TauCeti.restrictedHaar`,
   `TauCeti.exists_unique_restrictedHaar`): assuming `μ i (B i) = 1` for all but finitely many `i`,
   there exists a unique left Haar measure `ν` on `Πʳ i, [G i, B i]` whose value on any measurable
   coordinate box `RestrictedProduct.box C` agreeing with `B i` outside a finite set `T` (containing
   the non-compact or unnormalized places) is `∏ i ∈ T, μ i (C i)`. When `μ i (B i) = 1` for all
   `i`, this simplifies to the finitary product `∏ᶠ i, μ i (C i)`
   (`TauCeti.restrictedHaar_box_eq_finprod`).

2. **Convergent restricted Haar product** (`TauCeti.convergentHaarProduct`,
   `TauCeti.exists_unique_convergentHaarProduct`): assuming only the absolute convergence
   `Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|` outside a finite set `S` (as
   arises from local gauge measures before introducing Euler-factor convergence weights, or after
   multiplying by convergence factors), there exists a unique left Haar measure `ν` on
   `Πʳ i, [G i, B i]` satisfying, for every finite set `T ⊇ S` and every measurable box `box C` with
   `C i = B i` outside `T`, the product formula
   `ν (box C) = (∏ i ∈ T, μ i (C i)) *`
   `ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)`.

We also prove:
* **Independence of the finite exceptional set** (`TauCeti.convergentHaarProduct_of_subset`,
  `TauCeti.convergentHaarProduct_congr_finset`): enlarging or changing `S` leaves
  `convergentHaarProduct` unchanged.
* **Independence of the integral model** (`TauCeti.map_restrictedProductCongr_restrictedHaar`,
  `TauCeti.map_restrictedProductCongr_convergentHaarProduct`): replacing a family of compact-open
  subgroups `U` by any cofinitely equal family `U'` transports `restrictedHaar` and
  `convergentHaarProduct` along `TauCeti.restrictedProductCongr` with no scalar factor.
* **Unimodularity inheritance** (`TauCeti.isMulRightInvariant_restrictedHaar`,
  `TauCeti.isMulRightInvariant_convergentHaarProduct`): if every local Haar measure `μ i` is right
  invariant, so are `restrictedHaar` and `convergentHaarProduct`.

Every definition and theorem has an additive counterpart (`TauCeti.restrictedAddHaar`,
`TauCeti.convergentAddHaarProduct`, …) via `@[to_additive]`, covering restricted products of locally
compact additive groups relative to open additive subgroups or subrings (such as adele rings).

## Main definitions and results

* `TauCeti.principalProdEquiv`, `TauCeti.levelMonoidHom`: open-embedding homomorphism from
  `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)` into `Πʳ i, [G i, B i]`.
* `TauCeti.exists_unique_restrictedHaar`, `TauCeti.restrictedHaar`, `TauCeti.restrictedHaar_box`,
  `TauCeti.restrictedHaar_box_eq_finprod`, `TauCeti.comap_levelMonoidHom_restrictedHaar`,
  `TauCeti.map_restrictedProductCongr_restrictedHaar`.
* `TauCeti.exists_unique_convergentHaarProduct`, `TauCeti.convergentHaarProduct`,
  `TauCeti.convergentHaarProduct_box`, `TauCeti.convergentHaarProduct_of_subset`,
  `TauCeti.convergentHaarProduct_congr_finset`, `TauCeti.convergentHaarProduct_eq_restrictedHaar`,
  `TauCeti.map_restrictedProductCongr_convergentHaarProduct`.

## References

* A. Weil, *Adeles and Algebraic Groups*, Progress in Mathematics 23, Birkhäuser (1982),
  Chapter II, §§2.1–2.3.
* V. Platonov, A. Rapinchuk, and I. Rapinchuk, *Algebraic Groups and Number Theory*, Vol. 1,
  2nd ed., Cambridge University Press (2023), §3.5, pp. 188–195.
* A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16
  (1963), 5–30, §1.
-/

public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure RestrictedProduct Set Topology
open scoped ENNReal NNReal Pointwise RestrictedProduct

namespace TauCeti

/-! ### Auxiliary facts on convergent positive real products and Haar uniqueness -/

private theorem summable_notMem_of_subset {ι : Type*} {S T : Finset ι} (hST : S ⊆ T)
    (g : ι → ℝ) (hconv : Summable fun i : {i // i ∉ S} ↦ g i.1) :
    Summable fun i : {i // i ∉ T} ↦ g i.1 := by
  refine hconv.comp_injective (i := fun i : {i // i ∉ T} ↦ ⟨i.1, fun hiS ↦ i.2 (hST hiS)⟩) ?_
  intro a b h
  dsimp only at h
  exact Subtype.ext (Subtype.mk.inj h)

private theorem summable_log_of_summable_abs_sub_one {α : Type*} {f : α → ℝ}
    (hconv : Summable fun a ↦ |f a - 1|) :
    Summable fun a ↦ Real.log (f a) := by
  have hsub : Summable fun a ↦ f a - 1 := hconv.of_abs
  simpa only [add_sub_cancel] using Real.summable_log_one_add_of_summable hsub

private theorem tprod_eq_rexp_tsum_log_of_summable_abs_sub_one {α : Type*} {f : α → ℝ}
    (hf : ∀ a, 0 < f a) (hconv : Summable fun a ↦ |f a - 1|) :
    ∏' a, f a = Real.exp (∑' a, Real.log (f a)) :=
  (Real.rexp_tsum_eq_tprod hf (summable_log_of_summable_abs_sub_one hconv)).symm

private theorem tprod_pos_of_summable_abs_sub_one {α : Type*} {f : α → ℝ}
    (hf : ∀ a, 0 < f a) (hconv : Summable fun a ↦ |f a - 1|) :
    0 < ∏' a, f a := by
  rw [tprod_eq_rexp_tsum_log_of_summable_abs_sub_one hf hconv]
  exact Real.exp_pos _

private theorem tprod_split_finset {ι : Type*} [DecidableEq ι] {S T : Finset ι} (hST : S ⊆ T)
    (f : ι → ℝ) (hf : ∀ i ∉ S, 0 < f i)
    (hconv : Summable fun i : {i // i ∉ S} ↦ |f i.1 - 1|) :
    (∏' i : {i // i ∉ S}, f i.1) =
      (∏ i ∈ T \ S, f i) * (∏' i : {i // i ∉ T}, f i.1) := by
  have hconvT : Summable fun i : {i // i ∉ T} ↦ |f i.1 - 1| :=
    summable_notMem_of_subset hST (fun i ↦ |f i - 1|) hconv
  let s : Set {i // i ∉ S} := {x | x.1 ∈ T}
  let e₁ : s ≃ ↥(T \ S) :=
    { toFun x := ⟨x.1.1, Finset.mem_sdiff.mpr ⟨x.2, x.1.2⟩⟩
      invFun y := ⟨⟨y.1, (Finset.mem_sdiff.mp y.2).2⟩, (Finset.mem_sdiff.mp y.2).1⟩
      left_inv _ := by ext; rfl
      right_inv _ := by ext; rfl }
  let e₂ : ↑sᶜ ≃ {i // i ∉ T} :=
    { toFun x := ⟨x.1.1, x.2⟩
      invFun y := ⟨⟨y.1, fun hiS ↦ y.2 (hST hiS)⟩, y.2⟩
      left_inv _ := by ext; rfl
      right_inv _ := by ext; rfl }
  have _ : Fintype s := Fintype.ofEquiv _ e₁.symm
  have hs : Multipliable (fun x : s ↦ f x.1.1) := (hasProd_fintype _).multipliable
  have hT_mult : Multipliable (fun y : {i // i ∉ T} ↦ f y.1) :=
    Real.multipliable_of_summable_log (fun y ↦ hf y.1 fun hiS ↦ y.2 (hST hiS))
      (summable_log_of_summable_abs_sub_one hconvT)
  have hsc : Multipliable (fun x : ↑sᶜ ↦ f x.1.1) := e₂.multipliable_iff.mpr hT_mult
  rw [← Multipliable.tprod_mul_tprod_compl (f := fun x : {i // i ∉ S} ↦ f x.1) hs hsc]
  congr 1
  · rw [tprod_fintype]
    exact (e₁.prod_comp (fun y : ↥(T \ S) ↦ f y.1)).trans (Finset.prod_coe_sort (T \ S) f)
  · exact e₂.tprod_eq fun y ↦ f y.1

@[to_additive]
private theorem isMulLeftInvariant_eq_of_apply_eq {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (μ' μ : Measure H)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ']
    {s : Set H} (h₀ : μ s ≠ 0) (htop : μ s ≠ ⊤) (hs : μ' s = μ s) :
    μ' = μ := by
  rw [isMulLeftInvariant_eq_smul μ' μ] at hs ⊢
  have hc : (haarScalarFactor μ' μ : ℝ≥0∞) * μ s = 1 * μ s := by simpa using hs
  rw [ENNReal.mul_left_inj h₀ htop, ENNReal.coe_eq_one] at hc
  rw [hc, one_smul]

@[to_additive]
private theorem isHaarMeasure_comap {G H : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul G] [Group H] [TopologicalSpace H]
    [MeasurableSpace H] [BorelSpace H] [MeasurableMul H] (μ : Measure H) [IsHaarMeasure μ]
    {f : G →* H} (hf : IsOpenEmbedding f) :
    (μ.comap f).IsHaarMeasure :=
  @IsHaarMeasure.comap G H _ _ _ _ _ _ _ _ _ ‹_› μ _ f hf

private theorem nnreal_smul_measure_apply {X : Type*} {_ : MeasurableSpace X}
    (c : ℝ≥0) (μ : Measure X) (s : Set X) :
    (c • μ) s = (c : ℝ≥0∞) * μ s := by
  rw [_root_.smul_apply, ENNReal.smul_def, smul_eq_mul]

@[to_additive]
private theorem exists_isCompact_isClosed_mem_nhds_one {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] :
    ∃ U : Set H, IsCompact U ∧ IsClosed U ∧ U ∈ 𝓝 (1 : H) := by
  obtain ⟨V, hVcomp, hVnhds⟩ := exists_compact_mem_nhds (1 : H)
  exact ⟨closure V, hVcomp.closure, isClosed_closure, mem_of_superset hVnhds subset_closure⟩

private instance {X S : Type*} [TopologicalSpace X] [SecondCountableTopology X] [SetLike S X]
    (s : S) : SecondCountableTopology s :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

@[to_additive]
private instance {G S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SetLike S G] [SubgroupClass S G] (s : S) : IsTopologicalGroup s :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup (SubmonoidClass.subtype s)

private theorem isProbabilityMeasure_comap_subtype {X S : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [SetLike S X] (s : S) (hs : IsOpen (s : Set X))
    (μ : Measure X) (hμ : μ s = 1) :
    IsProbabilityMeasure (μ.comap (Subtype.val : s → X)) :=
  ⟨((MeasurableEmbedding.subtype_coe hs.measurableSet).comap_apply μ univ).trans
    (by rw [Subtype.coe_image_univ, hμ])⟩

/-! ### Principal-level topological group decomposition -/

section PrincipalLevel

variable {ι : Type*} {G : ι → Type*} {K : ι → Type*} [∀ i, SetLike (K i) (G i)]
variable [∀ i, Group (G i)] [∀ i, SubgroupClass (K i) (G i)] [∀ i, TopologicalSpace (G i)]

/-- For any finite index set `T : Finset ι`, the principal stage `Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`
is isomorphic as a topological group to `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. -/
@[to_additive principalProdAddEquiv /-- For any finite index set `T : Finset ι`, the principal stage
`Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]` is isomorphic as a topological additive group to
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)`. -/]
def principalProdEquiv (B : ∀ i, K i) (T : Finset ι) :
    ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) ≃ₜ* Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ] :=
  open Classical in
  { toFun p := mk (fun i ↦ if hi : i ∈ T then p.1 ⟨i, hi⟩ else (p.2 ⟨i, hi⟩ : G i)) <|
      eventually_principal.mpr fun i hi ↦ by
        have hiT : i ∉ T := Finset.mem_coe.not.mp hi
        simp [hiT]
    invFun x :=
      ((fun i : T ↦ x i.1),
        fun i : {i // i ∉ T} ↦ ⟨x i.1,
          eventually_principal.mp x.eventually i.1 (Finset.mem_coe.not.mpr i.2)⟩)
    left_inv p := by
      ext i
      · simp [i.2]
      · simp [i.2]
    right_inv x := by
      ext i
      simp only [mk_apply]
      split_ifs <;> rfl
    map_mul' p q := by
      ext i
      by_cases hi : i ∈ T <;> simp [hi]
    continuous_toFun := by
      refine isEmbedding_coe_of_principal.continuous_iff.mpr (continuous_pi fun i ↦ ?_)
      by_cases hi : i ∈ T <;> simp only [Function.comp_def, mk_apply, hi, ↓reduceDIte] <;> fun_prop
    continuous_invFun := Continuous.prodMk
      (continuous_pi fun i ↦ (continuous_apply i.1).comp continuous_coe)
      (continuous_pi fun i ↦ Continuous.subtype_mk ((continuous_apply i.1).comp continuous_coe) _) }

/-- The open-embedding group homomorphism from `(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)` into
the cofinite restricted product `Πʳ i, [G i, B i]`, factoring through the principal stage
`Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`. -/
@[to_additive /-- The open-embedding additive group homomorphism from
`(Π i : T, G i) × (Π i : {i // i ∉ T}, B i)` into the cofinite restricted product
`Πʳ i, [G i, B i]`, factoring through the principal stage `Πʳ i, [G i, B i]_[𝓟 (T : Set ι)ᶜ]`. -/]
def levelMonoidHom (B : ∀ i, K i) (T : Finset ι) :
    ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) →* Πʳ i, [G i, B i] where
  toFun p :=
    inclusion G (fun i ↦ (B i : Set (G i)))
      (le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite) (principalProdEquiv B T p)
  map_one' := by
    ext i
    simp only [inclusion_apply, principalProdEquiv, ContinuousMulEquiv.coe_mk, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, mk_apply, one_apply]
    split_ifs <;> rfl
  map_mul' p q := by
    ext i
    simpa only [inclusion_apply, mul_apply] using
      congr_arg (fun x ↦ x i) (map_mul (principalProdEquiv B T) p q)

/-- Coordinate formula for `levelMonoidHom B T` at `i ∈ T`. -/
@[to_additive (attr := simp) /-- Coordinate formula for `levelAddMonoidHom B T` at `i ∈ T`. -/]
theorem levelMonoidHom_apply_of_mem (B : ∀ i, K i) (T : Finset ι)
    (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) {i : ι} (hi : i ∈ T) :
    levelMonoidHom B T p i = p.1 ⟨i, hi⟩ := by
  simp [levelMonoidHom, principalProdEquiv, hi]

/-- Coordinate formula for `levelMonoidHom B T` at `i ∉ T`. -/
@[to_additive (attr := simp) /-- Coordinate formula for `levelAddMonoidHom B T` at `i ∉ T`. -/]
theorem levelMonoidHom_apply_of_notMem (B : ∀ i, K i) (T : Finset ι)
    (p : (Π i : T, G i) × (Π i : {i // i ∉ T}, B i)) {i : ι} (hi : i ∉ T) :
    levelMonoidHom B T p i = (p.2 ⟨i, hi⟩ : G i) := by
  simp [levelMonoidHom, principalProdEquiv, hi]

/-- When each reference subgroup `B i` is open, `levelMonoidHom B T` is an open topological
embedding into `Πʳ i, [G i, B i]`. -/
@[to_additive /-- When each reference additive subgroup `B i` is open, `levelAddMonoidHom B T` is an
open topological embedding into `Πʳ i, [G i, B i]`. -/]
theorem isOpenEmbedding_levelMonoidHom (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))] (T : Finset ι) :
    IsOpenEmbedding (levelMonoidHom B T) :=
  (isOpenEmbedding_inclusion_principal hBopen.out
    (le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite)).comp
    (principalProdEquiv B T).toHomeomorph.isOpenEmbedding

/-- For any family of sets `C : ∀ i, Set (G i)` agreeing with `B i` outside `T`, the image of
`(Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ` under `levelMonoidHom B T` is `box C`. -/
@[to_additive image_levelAddMonoidHom_pi_prod_univ /-- For any family of sets `C : ∀ i, Set (G i)`
agreeing with `B i` outside `T`, the image of `(Set.univ.pi fun i : T ↦ C i.1) ×ˢ Set.univ` under
`levelAddMonoidHom B T` is `box C`. -/]
theorem image_levelMonoidHom_pi_prod_univ (B : ∀ i, K i) (T : Finset ι) {C : ∀ i, Set (G i)}
    (hCB : ∀ i ∉ T, C i = B i) :
    levelMonoidHom B T '' ((univ.pi fun i : T ↦ C i.1) ×ˢ univ) =
      (box C : Set (Πʳ i, [G i, B i])) := by
  ext x
  simp only [mem_image, mem_prod, Set.mem_pi, mem_univ, forall_true_left, and_true, mem_box]
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨p, hp, rfl⟩ i
    by_cases hi : i ∈ T
    · simpa [hi] using hp ⟨i, hi⟩
    · rw [levelMonoidHom_apply_of_notMem B T p hi, hCB i hi]
      exact (p.2 ⟨i, hi⟩).2
  · have hxB (i : {i // i ∉ T}) : x i.1 ∈ B i.1 := by
      have hxi : x i.1 ∈ (B i.1 : Set (G i.1)) := hCB i.1 i.2 ▸ hx i.1
      exact hxi
    refine ⟨((fun i : T ↦ x i.1), fun i : {i // i ∉ T} ↦ ⟨x i.1, hxB i⟩), fun i ↦ hx i.1, ?_⟩
    ext i
    by_cases hi : i ∈ T <;> simp [hi]

end PrincipalLevel

/-! ### Normalized restricted products of local Haar measures -/

section NormalizedRestrictedHaar

variable {ι : Type*} [Countable ι]
variable {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
variable {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- On a restricted product `Πʳ i, [G i, B i]` where `B i` is compact and `μ i (B i) = 1` at all
but finitely many indices, there exists a unique left Haar measure `ν` assigning measure
`∏ i ∈ T, μ i (C i)` to every measurable box `box C` agreeing with `B i` outside a finite set `T`
that contains all non-compact or unnormalized places. -/
@[to_additive /-- On a restricted product `Πʳ i, [G i, B i]` of locally compact additive groups
where `B i` is compact and `μ i (B i) = 1` at all but finitely many indices, there exists a unique
left-invariant additive Haar measure `ν` assigning measure `∏ i ∈ T, μ i (C i)` to every measurable
box `box C` agreeing with `B i` outside a finite set `T` that contains all non-compact or
unnormalized places. -/]
theorem exists_unique_restrictedHaar (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    ∃! ν : Measure (Πʳ i, [G i, B i]),
      ν.IsHaarMeasure ∧
      ∀ (T : Finset ι), (∀ i ∉ T, IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1) →
        ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) → (∀ i ∉ T, C i = B i) →
          ν (box C) = ∏ i ∈ T, μ i (C i) := by
  classical
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact
  let S₀ : Finset ι := (mem_cofinite.mp (hBcompact.and hμB)).toFinset
  have hS₀ (i : ι) (hi : i ∉ S₀) : IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1 := by
    by_contra hnot
    exact hi ((Set.Finite.mem_toFinset _).mpr hnot)
  choose K₀ hK₀_comp hK₀_closed hK₀_nhds using fun i : ι ↦
    exists_isCompact_isClosed_mem_nhds_one (H := G i)
  let Kref : ∀ i, Set (G i) := fun i ↦ if i ∈ S₀ then K₀ i else (B i : Set (G i))
  have hKref_comp (i : ι) : IsCompact (Kref i) := by
    by_cases hi : i ∈ S₀
    · simpa [Kref, hi] using hK₀_comp i
    · simpa [Kref, hi] using (hS₀ i hi).1
  have hKref_meas (i : ι) : MeasurableSet (Kref i) := by
    by_cases hi : i ∈ S₀
    · simpa [Kref, hi] using (hK₀_closed i).measurableSet
    · simpa [Kref, hi] using (hBopen.out i).measurableSet
  have hKref_eq (i : ι) (hi : i ∉ S₀) : Kref i = B i := by simp [Kref, hi]
  have hKref_one_int (i : ι) : (1 : G i) ∈ interior (Kref i) := by
    by_cases hi : i ∈ S₀
    · simpa [Kref, hi] using mem_interior_iff_mem_nhds.mpr (hK₀_nhds i)
    · simp only [Kref, hi, ↓reduceIte, (hBopen.out i).interior_eq]
      exact one_mem (B i)
  have hKref_pos (i : ι) : 0 < μ i (Kref i) :=
    (isOpen_interior.measure_pos (μ i) ⟨1, hKref_one_int i⟩).trans_le (measure_mono interior_subset)
  have hKref_lt_top (i : ι) : μ i (Kref i) < ⊤ := (hKref_comp i).measure_lt_top
  have hboxK_comp : IsCompact (box Kref : Set (Πʳ i, [G i, B i])) := by
    refine isCompact_box hKref_comp ?_
    filter_upwards [S₀.finite_toSet.compl_mem_cofinite] with i hi
    exact (hKref_eq i hi).subset
  have hboxK_int : (interior (box Kref : Set (Πʳ i, [G i, B i]))).Nonempty := by
    refine ⟨1, box_interior_subset_interior_box ?_ (mem_box.mpr fun i ↦ hKref_one_int i)⟩
    filter_upwards [S₀.finite_toSet.compl_mem_cofinite] with i hi
    have hi' : i ∉ S₀ := hi
    simp [Kref, hi', (hBopen.out i).interior_eq]
  let Kpos : TopologicalSpace.PositiveCompacts (Πʳ i, [G i, B i]) :=
    ⟨⟨box Kref, hboxK_comp⟩, hboxK_int⟩
  let c₀ : ℝ≥0 := ∏ i ∈ S₀, (μ i (Kref i)).toNNReal
  have hc₀_pos : 0 < c₀ := Finset.prod_pos fun i _ ↦
    ENNReal.toNNReal_pos (hKref_pos i).ne' (hKref_lt_top i).ne
  let ν : Measure (Πʳ i, [G i, B i]) := c₀ • haarMeasure Kpos
  have hν_haar : ν.IsHaarMeasure := IsHaarMeasure.nnreal_smul (haarMeasure Kpos) hc₀_pos.ne'
  have hprod_S₀_pos : 0 < ∏ i ∈ S₀, μ i (Kref i) :=
    CanonicallyOrderedAdd.prod_pos.mpr fun i _ ↦ hKref_pos i
  have hprod_S₀_lt_top : (∏ i ∈ S₀, μ i (Kref i)) < ⊤ :=
    ENNReal.prod_lt_top fun i _ ↦ hKref_lt_top i
  have hν_Kref : ν (box Kref) = ∏ i ∈ S₀, μ i (Kref i) := by
    have hself : haarMeasure Kpos (box Kref) = 1 := haarMeasure_self
    dsimp only [ν]
    rw [_root_.smul_apply, hself, ENNReal.smul_one, ENNReal.ofNNReal_finsetProd]
    exact Finset.prod_congr rfl fun i _ ↦ ENNReal.coe_toNNReal (hKref_lt_top i).ne
  have hcomap_eq (T : Finset ι) (hS₀T : S₀ ⊆ T) :
      ν.comap (levelMonoidHom B T) =
        (Measure.pi fun i : T ↦ μ i.1).prod
          (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.1).comap Subtype.val) := by
    have hT (i : {i // i ∉ T}) : IsCompact (B i.1 : Set (G i.1)) ∧ μ i.1 (B i.1) = 1 :=
      hS₀ i.1 fun hiS₀ ↦ i.2 (hS₀T hiS₀)
    have _ (i : {i // i ∉ T}) : CompactSpace (B i.1) := isCompact_iff_compactSpace.mp (hT i).1
    have _ : LocallyCompactSpace (Π i : {i // i ∉ T}, B i.1) := by
      have _ : WeaklyLocallyCompactSpace (Π i : {i // i ∉ T}, B i.1) := inferInstance
      infer_instance
    have _ (i : {i // i ∉ T}) : ((μ i.1).comap Subtype.val).IsHaarMeasure :=
      isHaarMeasure_comap (μ i.1) (f := SubmonoidClass.subtype (B i.1))
        (hBopen.out i.1).isOpenEmbedding_subtypeVal
    have _ (i : {i // i ∉ T}) :
        IsProbabilityMeasure ((μ i.1).comap (Subtype.val : B i.1 → G i.1)) :=
      isProbabilityMeasure_comap_subtype (B i.1) (hBopen.out i.1) (μ i.1) (hT i).2
    have _ : (ν.comap (levelMonoidHom B T)).IsHaarMeasure :=
      isHaarMeasure_comap ν (isOpenEmbedding_levelMonoidHom B T)
    let E_K : Set ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i.1)) :=
      (univ.pi fun i : T ↦ Kref i.1) ×ˢ univ
    have hprod_EK : ((Measure.pi fun i : T ↦ μ i.1).prod
        (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.1).comap Subtype.val)) E_K =
          ∏ i ∈ S₀, μ i (Kref i) := by
      rw [Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
        Finset.prod_coe_sort T fun i ↦ μ i (Kref i)]
      exact (Finset.prod_subset hS₀T fun i _ hiS₀ ↦ by rw [hKref_eq i hiS₀, (hS₀ i hiS₀).2]).symm
    have hμ_EK : (ν.comap (levelMonoidHom B T)) E_K = ∏ i ∈ S₀, μ i (Kref i) := by
      rw [(isOpenEmbedding_levelMonoidHom B T).measurableEmbedding.comap_apply,
        image_levelMonoidHom_pi_prod_univ B T fun i hiT ↦ hKref_eq i fun hiS₀ ↦ hiT (hS₀T hiS₀),
        hν_Kref]
    exact isMulLeftInvariant_eq_of_apply_eq _ _
      (hprod_EK ▸ hprod_S₀_pos.ne') (hprod_EK ▸ hprod_S₀_lt_top.ne) (hμ_EK.trans hprod_EK.symm)
  have hν_box (T : Finset ι) (hT : ∀ i ∉ T, IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1)
      (C : ∀ i, Set (G i)) (_ : ∀ i, MeasurableSet (C i)) (hCB : ∀ i ∉ T, C i = B i) :
      ν (box C) = ∏ i ∈ T, μ i (C i) := by
    let T' : Finset ι := S₀ ∪ T
    have hS₀T' : S₀ ⊆ T' := Finset.subset_union_left
    have hTT' : T ⊆ T' := Finset.subset_union_right
    have hCB' (i : ι) (hi : i ∉ T') : C i = B i := hCB i fun hiT ↦ hi (hTT' hiT)
    have _ (i : {i // i ∉ T'}) :
        IsProbabilityMeasure ((μ i.1).comap (Subtype.val : B i.1 → G i.1)) :=
      isProbabilityMeasure_comap_subtype (B i.1) (hBopen.out i.1) (μ i.1)
        (hS₀ i.1 fun hiS₀ ↦ i.2 (hS₀T' hiS₀)).2
    rw [← image_levelMonoidHom_pi_prod_univ B T' hCB',
      ← (isOpenEmbedding_levelMonoidHom B T').measurableEmbedding.comap_apply,
      hcomap_eq T' hS₀T', Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
      Finset.prod_coe_sort T' fun i ↦ μ i (C i)]
    exact (Finset.prod_subset hTT' fun i _ hiT ↦ by rw [hCB i hiT, (hT i hiT).2]).symm
  refine ⟨ν, ⟨hν_haar, hν_box⟩, ?_⟩
  rintro ν' ⟨hν'_haar, hν'_box⟩
  exact isMulLeftInvariant_eq_of_apply_eq ν' ν
    (hν_Kref ▸ hprod_S₀_pos.ne') (hν_Kref ▸ hprod_S₀_lt_top.ne)
    ((hν'_box S₀ hS₀ Kref hKref_meas hKref_eq).trans hν_Kref.symm)

/-- The canonical restricted Haar measure on `Πʳ i, [G i, B i]` attached to local Haar measures
`μ i` normalized by `μ i (B i) = 1` at all but finitely many indices. -/
@[to_additive /-- The canonical restricted additive Haar measure on `Πʳ i, [G i, B i]` attached to
local additive Haar measures `μ i` normalized by `μ i (B i) = 1` at all but finitely many
indices. -/]
def restrictedHaar (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    Measure (Πʳ i, [G i, B i]) :=
  (exists_unique_restrictedHaar B hBcompact μ hμB).choose

/-- `restrictedHaar` is a left Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `restrictedAddHaar` is a left-invariant additive Haar measure on
`Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_restrictedHaar (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B hBcompact μ hμB).IsHaarMeasure :=
  (exists_unique_restrictedHaar B hBcompact μ hμB).choose_spec.1.1

/-- Value of `restrictedHaar` on a measurable coordinate box `box C` agreeing with `B i` outside a
finite set `T` that contains all non-compact or unnormalized places. -/
@[to_additive /-- Value of `restrictedAddHaar` on a measurable coordinate box `box C` agreeing with
`B i` outside a finite set `T` that contains all non-compact or unnormalized places. -/]
theorem restrictedHaar_box (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCmeas : ∀ i, MeasurableSet (C i)) (hCB : ∀ i ∉ T, C i = B i) :
    restrictedHaar B hBcompact μ hμB (box C) = ∏ i ∈ T, μ i (C i) :=
  (exists_unique_restrictedHaar B hBcompact μ hμB).choose_spec.1.2 T hT C hCmeas hCB

/-- Uniqueness of `restrictedHaar`: any left Haar measure satisfying the finite-level box formula
coincides with `restrictedHaar`. -/
@[to_additive /-- Uniqueness of `restrictedAddHaar`: any left-invariant additive Haar measure
satisfying the finite-level box formula coincides with `restrictedAddHaar`. -/]
theorem restrictedHaar_unique (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {ν : Measure (Πʳ i, [G i, B i])} [ν.IsHaarMeasure]
    (hν : ∀ (T : Finset ι), (∀ i ∉ T, IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1) →
      ∀ C : ∀ i, Set (G i), (∀ i, MeasurableSet (C i)) → (∀ i ∉ T, C i = B i) →
        ν (box C) = ∏ i ∈ T, μ i (C i)) :
    ν = restrictedHaar B hBcompact μ hμB :=
  (exists_unique_restrictedHaar B hBcompact μ hμB).choose_spec.2 ν ⟨inferInstance, hν⟩

/-- When `μ i (B i) = 1` at *every* index `i`, `restrictedHaar` evaluates on any measurable box
`box C` agreeing cofinitely with `B i` as the finitary product `∏ᶠ i, μ i (C i)`. -/
@[to_additive restrictedAddHaar_box_eq_finprod /-- When `μ i (B i) = 1` at *every* index `i`,
`restrictedAddHaar` evaluates on any measurable box `box C` agreeing cofinitely with `B i` as the
finitary product `∏ᶠ i, μ i (C i)`. -/]
theorem restrictedHaar_box_eq_finprod (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] (hμB : ∀ i, μ i (B i) = 1)
    {C : ∀ i, Set (G i)} (hCmeas : ∀ i, MeasurableSet (C i))
    (hCB : ∀ᶠ i in cofinite, C i = B i) :
    restrictedHaar B hBcompact μ (.of_forall hμB) (box C) = ∏ᶠ i, μ i (C i) := by
  classical
  let T : Finset ι := (mem_cofinite.mp (hBcompact.and hCB)).toFinset
  have hT_comp (i : ι) (hi : i ∉ T) : IsCompact (B i : Set (G i)) ∧ C i = B i := by
    by_contra hnot
    exact hi ((Set.Finite.mem_toFinset _).mpr hnot)
  rw [restrictedHaar_box B hBcompact μ (.of_forall hμB)
    (fun i hi ↦ ⟨(hT_comp i hi).1, hμB i⟩) hCmeas (fun i hi ↦ (hT_comp i hi).2)]
  symm
  refine finprod_eq_prod_of_mulSupport_subset _ (s := T) fun i hi ↦ ?_
  by_contra hiT
  refine hi ?_
  dsimp only
  rw [(hT_comp i hiT).2, hμB i]

/-- When `μ i (B i) = 1` at every index, the everywhere-integral box `box B` has `restrictedHaar`
measure `1`. -/
@[to_additive (attr := simp) /-- When `μ i (B i) = 1` at every index, the everywhere-integral box
`box B` has `restrictedAddHaar` measure `1`. -/]
theorem restrictedHaar_box_self (B : ∀ i, K i) [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] (hμB : ∀ i, μ i (B i) = 1) :
    restrictedHaar B hBcompact μ (.of_forall hμB) (box fun i ↦ (B i : Set (G i))) = 1 := by
  rw [restrictedHaar_box_eq_finprod B hBcompact μ hμB (fun i ↦ (hBopen.out i).measurableSet)
    (.of_forall fun _ ↦ rfl)]
  simp [hμB]

/-- Pulling `restrictedHaar` back along `levelMonoidHom B T` recovers the product of the finite
product Haar measure on `Π i : T, G i` with Kolmogorov's infinite product probability Haar measure
on `Π i : {i // i ∉ T}, B i`. -/
@[to_additive /-- Pulling `restrictedAddHaar` back along `levelAddMonoidHom B T` recovers the
product of the finite product additive Haar measure on `Π i : T, G i` with Kolmogorov's infinite
product probability additive Haar measure on `Π i : {i // i ∉ T}, B i`. -/]
theorem comap_levelMonoidHom_restrictedHaar (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
    {T : Finset ι} (hT : ∀ i ∉ T, IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1) :
    (restrictedHaar B hBcompact μ hμB).comap (levelMonoidHom B T) =
      (Measure.pi fun i : T ↦ μ i.1).prod
        (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.1).comap Subtype.val) := by
  classical
  have _ (i : {i // i ∉ T}) : CompactSpace (B i.1) := isCompact_iff_compactSpace.mp (hT i.1 i.2).1
  have _ : LocallyCompactSpace (Π i : {i // i ∉ T}, B i.1) := by
    have _ : WeaklyLocallyCompactSpace (Π i : {i // i ∉ T}, B i.1) := inferInstance
    infer_instance
  have _ (i : {i // i ∉ T}) : ((μ i.1).comap Subtype.val).IsHaarMeasure :=
    isHaarMeasure_comap (μ i.1) (f := SubmonoidClass.subtype (B i.1))
      (hBopen.out i.1).isOpenEmbedding_subtypeVal
  have _ (i : {i // i ∉ T}) :
      IsProbabilityMeasure ((μ i.1).comap (Subtype.val : B i.1 → G i.1)) :=
    isProbabilityMeasure_comap_subtype (B i.1) (hBopen.out i.1) (μ i.1) (hT i.1 i.2).2
  have _ : ((restrictedHaar B hBcompact μ hμB).comap (levelMonoidHom B T)).IsHaarMeasure :=
    isHaarMeasure_comap (restrictedHaar B hBcompact μ hμB) (isOpenEmbedding_levelMonoidHom B T)
  choose K₀ hK₀_comp hK₀_closed hK₀_nhds using fun i : ι ↦
    exists_isCompact_isClosed_mem_nhds_one (H := G i)
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ T then K₀ i else (B i : Set (G i))
  have hCmeas (i : ι) : MeasurableSet (C i) := by
    by_cases hi : i ∈ T
    · simpa [C, hi] using (hK₀_closed i).measurableSet
    · simpa [C, hi] using (hBopen.out i).measurableSet
  have hCB (i : ι) (hi : i ∉ T) : C i = B i := by simp [C, hi]
  have hCpos (i : T) : 0 < μ i.1 (C i.1) := by
    simp only [C, i.2, ↓reduceIte]
    exact (isOpen_interior.measure_pos (μ i.1)
      ⟨1, mem_interior_iff_mem_nhds.mpr (hK₀_nhds i.1)⟩).trans_le (measure_mono interior_subset)
  have hClt (i : T) : μ i.1 (C i.1) < ⊤ := by
    simp only [C, i.2, ↓reduceIte]
    exact (hK₀_comp i.1).measure_lt_top
  let E : Set ((Π i : T, G i) × (Π i : {i // i ∉ T}, B i.1)) :=
    (univ.pi fun i : T ↦ C i.1) ×ˢ univ
  have hprod_E : ((Measure.pi fun i : T ↦ μ i.1).prod
      (Measure.infinitePi fun i : {i // i ∉ T} ↦ (μ i.1).comap Subtype.val)) E =
        ∏ i ∈ T, μ i (C i) := by
    rw [Measure.prod_prod, Measure.pi_pi, measure_univ, mul_one,
      Finset.prod_coe_sort T fun i ↦ μ i (C i)]
  have hμ : ((restrictedHaar B hBcompact μ hμB).comap (levelMonoidHom B T)) E =
      ∏ i ∈ T, μ i (C i) := by
    rw [(isOpenEmbedding_levelMonoidHom B T).measurableEmbedding.comap_apply,
      image_levelMonoidHom_pi_prod_univ B T hCB,
      restrictedHaar_box B hBcompact μ hμB hT hCmeas hCB]
  have hpos : 0 < ∏ i ∈ T, μ i (C i) :=
    (Finset.prod_coe_sort T fun i ↦ μ i (C i)) ▸
      CanonicallyOrderedAdd.prod_pos.mpr fun i _ ↦ hCpos i
  have hlt : (∏ i ∈ T, μ i (C i)) < ⊤ :=
    (Finset.prod_coe_sort T fun i ↦ μ i (C i)) ▸ ENNReal.prod_lt_top fun i _ ↦ hClt i
  exact isMulLeftInvariant_eq_of_apply_eq _ _ (hprod_E ▸ hpos.ne') (hprod_E ▸ hlt.ne)
    (hμ.trans hprod_E.symm)

/-- If every local Haar measure `μ i` is right-invariant (i.e. each `G i` is unimodular), then
`restrictedHaar` is also right-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is right-translation-invariant, then
`restrictedAddHaar` is also right-translation-invariant. -/]
instance isMulRightInvariant_restrictedHaar (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (hBcompact : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1) :
    (restrictedHaar B hBcompact μ hμB).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    classical
    have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact
    set ν := restrictedHaar B hBcompact μ hμB
    let T : Finset ι := (mem_cofinite.mp ((hBcompact.and hμB).and g.eventually)).toFinset
    have hT (i : ι) (hi : i ∉ T) :
        (IsCompact (B i : Set (G i)) ∧ μ i (B i) = 1) ∧ g i ∈ B i := by
      by_contra hnot
      exact hi ((Set.Finite.mem_toFinset _).mpr hnot)
    choose K₀ hK₀_comp hK₀_closed hK₀_nhds using fun i : ι ↦
      exists_isCompact_isClosed_mem_nhds_one (H := G i)
    let C : ∀ i, Set (G i) := fun i ↦ if i ∈ T then K₀ i else (B i : Set (G i))
    have hCmeas (i : ι) : MeasurableSet (C i) := by
      by_cases hi : i ∈ T
      · simpa [C, hi] using (hK₀_closed i).measurableSet
      · simpa [C, hi] using (hBopen.out i).measurableSet
    have hCB (i : ι) (hi : i ∉ T) : C i = B i := by simp [C, hi]
    have hνC_pos : 0 < ν (box C) := by
      rw [restrictedHaar_box B hBcompact μ hμB (fun i hi ↦ (hT i hi).1) hCmeas hCB,
        CanonicallyOrderedAdd.prod_pos]
      intro i hi
      simp only [C, hi, ↓reduceIte]
      exact (isOpen_interior.measure_pos (μ i)
        ⟨1, mem_interior_iff_mem_nhds.mpr (hK₀_nhds i)⟩).trans_le (measure_mono interior_subset)
    have hνC_lt : ν (box C) < ⊤ := by
      rw [restrictedHaar_box B hBcompact μ hμB (fun i hi ↦ (hT i hi).1) hCmeas hCB]
      refine ENNReal.prod_lt_top fun i hi ↦ ?_
      simp only [C, hi, ↓reduceIte]
      exact (hK₀_comp i).measure_lt_top
    let C' : ∀ i, Set (G i) := fun i ↦ (· * g i) ⁻¹' C i
    have hC'meas (i : ι) : MeasurableSet (C' i) := measurable_mul_const (g i) (hCmeas i)
    have hC'B (i : ι) (hi : i ∉ T) : C' i = B i := by
      ext x
      simp only [C', mem_preimage, hCB i hi, SetLike.mem_coe]
      exact mul_mem_cancel_right (hT i hi).2
    have hpre : (· * g) ⁻¹' (box C : Set (Πʳ i, [G i, B i])) = box C' := by
      ext x
      simp [C']
    refine isMulLeftInvariant_eq_of_apply_eq (ν.map (· * g)) ν hνC_pos.ne' hνC_lt.ne ?_
    rw [map_apply (measurable_mul_const g) (measurableSet_box hCmeas), hpre,
      restrictedHaar_box B hBcompact μ hμB (fun i hi ↦ (hT i hi).1) hC'meas hC'B,
      restrictedHaar_box B hBcompact μ hμB (fun i hi ↦ (hT i hi).1) hCmeas hCB]
    exact Finset.prod_congr rfl fun i _ ↦ measure_preimage_mul_right (μ i) (g i) (C i)

/-- **Independence of the integral model for `restrictedHaar`.** If two families of open subgroups
`U` and `U'` agree cofinitely, then `restrictedProductCongr U U' h` pushes `restrictedHaar` for `U`
directly to `restrictedHaar` for `U'` with no scalar factor. -/
@[to_additive map_addRestrictedProductCongr_restrictedAddHaar
/-- **Independence of the integral model for `restrictedAddHaar`.** If two families of open additive
subgroups `U` and `U'` agree cofinitely, then `addRestrictedProductCongr U U' h` pushes
`restrictedAddHaar` for `U` directly to `restrictedAddHaar` for `U'` with no scalar factor. -/]
theorem map_restrictedProductCongr_restrictedHaar
    (U U' : ∀ i, Subgroup (G i))
    [Fact (∀ i, IsOpen (U i : Set (G i)))] [Fact (∀ i, IsOpen (U' i : Set (G i)))]
    (h : ∀ᶠ i in cofinite, U i = U' i)
    (hUcompact : ∀ᶠ i in cofinite, IsCompact (U i : Set (G i)))
    (hU'compact : ∀ᶠ i in cofinite, IsCompact (U' i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμU : ∀ᶠ i in cofinite, μ i (U i) = 1)
    (hμU' : ∀ᶠ i in cofinite, μ i (U' i) = 1) :
    (restrictedHaar U hUcompact μ hμU).map (restrictedProductCongr U U' h) =
      restrictedHaar U' hU'compact μ hμU' := by
  classical
  let e : (Πʳ i, [G i, (U i : Set (G i))]) ≃ₜ* (Πʳ i, [G i, (U' i : Set (G i))]) :=
    { restrictedProductCongr U U' h with
      continuous_toFun := continuous_restrictedProductCongr U U' h
      continuous_invFun := continuous_restrictedProductCongr_symm U U' h }
  have h_haar : ((restrictedHaar U hUcompact μ hμU).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (restrictedHaar U hUcompact μ hμU)
  have _ : ((restrictedHaar U hUcompact μ hμU).map
      (restrictedProductCongr U U' h)).IsHaarMeasure := h_haar
  refine restrictedHaar_unique U' hU'compact μ hμU' fun T hT C hCmeas hCU' ↦ ?_
  let S₀ : Finset ι := (mem_cofinite.mp ((h.and hUcompact).and hμU)).toFinset
  let T' : Finset ι := T ∪ S₀
  have hTT' : T ⊆ T' := Finset.subset_union_left
  have hS₀ (i : ι) (hi : i ∉ T') :
      (U i = U' i ∧ IsCompact (U i : Set (G i))) ∧ μ i (U i) = 1 := by
    by_contra hnot
    exact hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
  have hpre : (restrictedProductCongr U U' h) ⁻¹'
      (box C : Set (Πʳ i, [G i, (U' i : Set (G i))])) =
      (box C : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
    ext x
    simp
  have hCU (i : ι) (hi : i ∉ T') : C i = U i := by
    rw [hCU' i fun hiT ↦ hi (hTT' hiT), ← (hS₀ i hi).1.1]
  rw [map_apply (continuous_restrictedProductCongr U U' h).measurable (measurableSet_box hCmeas),
    hpre, restrictedHaar_box U hUcompact μ hμU
      (fun i hi ↦ ⟨(hS₀ i hi).1.2, (hS₀ i hi).2⟩) hCmeas hCU]
  exact (Finset.prod_subset hTT' fun i _ hiT ↦ by rw [hCU' i hiT, (hT i hiT).2]).symm

end NormalizedRestrictedHaar

/-! ### Convergent restricted products of local Haar measures -/

section ConvergentHaarProduct

variable {ι : Type*} [Countable ι]
variable {G : ι → Type*} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
  [∀ i, SecondCountableTopology (G i)] [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
variable {K : ι → Type*} [∀ i, SetLike (K i) (G i)] [∀ i, SubgroupClass (K i) (G i)]

/-- **Convergent restricted product of local Haar measures.**
Given a finite exceptional set `S : Finset ι`, open subgroups `B i` that are compact outside `S`,
and local Haar measures `μ i` whose integral masses satisfy
`Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|`, there exists a unique left Haar
measure `ν` on `Πʳ i, [G i, B i]` such that for every finite set `T ⊇ S` and every family of
measurable sets `C i` agreeing with `B i` outside `T`,
`ν (box C) = (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)`.
-/
@[to_additive
/-- **Convergent restricted product of local additive Haar measures.**
Given a finite exceptional set `S : Finset ι`, open additive subgroups `B i` that are compact
outside `S`, and local additive Haar measures `μ i` whose integral masses satisfy
`Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|`, there exists a unique
left-invariant additive Haar measure `ν` on `Πʳ i, [G i, B i]` such that for every finite set
`T ⊇ S` and every family of measurable sets `C i` agreeing with `B i` outside `T`,
`ν (box C) = (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)`.
-/]
theorem exists_unique_convergentHaarProduct (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    ∃! ν : Measure (Πʳ i, [G i, B i]),
      ν.IsHaarMeasure ∧
      ∀ (T : Finset ι), S ⊆ T → ∀ C : ∀ i, Set (G i),
        (∀ i, MeasurableSet (C i)) → (∀ i ∉ T, C i = B i) →
        ν (box C) = (∏ i ∈ T, μ i (C i)) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) := by
  classical
  have hB_pos (i : ι) : 0 < μ i (B i) :=
    (hBopen.out i).measure_pos (μ i) ⟨1, one_mem (B i)⟩
  have hB_lt_top {i : ι} (hi : i ∉ S) : μ i (B i) < ⊤ := (hBcompact i hi).measure_lt_top
  have hB_toReal_pos {i : ι} (hi : i ∉ S) : 0 < (μ i (B i)).toReal :=
    ENNReal.toReal_pos (hB_pos i).ne' (hB_lt_top hi).ne
  have hBcompact' : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)) := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
    exact hBcompact i hi
  have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact'
  let μ' : ∀ i, Measure (G i) := fun i ↦
    if i ∈ S then μ i else ((μ i (B i)).toNNReal)⁻¹ • μ i
  have _ (i : ι) : (μ' i).IsHaarMeasure := by
    by_cases hi : i ∈ S
    · simp only [μ', hi, ↓reduceIte]
      infer_instance
    · simp only [μ', hi, ↓reduceIte]
      refine IsHaarMeasure.nnreal_smul (μ i) (inv_ne_zero ?_)
      exact (ENNReal.toNNReal_pos (hB_pos i).ne' (hB_lt_top hi).ne).ne'
  have hμ'B_out {i : ι} (hi : i ∉ S) : μ' i (B i) = 1 := by
    simp only [μ', hi, ↓reduceIte]
    rw [nnreal_smul_measure_apply, ENNReal.coe_inv
      (ENNReal.toNNReal_pos (hB_pos i).ne' (hB_lt_top hi).ne).ne',
      ENNReal.coe_toNNReal (hB_lt_top hi).ne]
    exact ENNReal.inv_mul_cancel (hB_pos i).ne' (hB_lt_top hi).ne
  have hμ'B : ∀ᶠ i in cofinite, μ' i (B i) = 1 := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
    exact hμ'B_out hi
  let cS_real : ℝ := ∏' i : {i // i ∉ S}, (μ i.1 (B i.1)).toReal
  have hcS_pos : 0 < cS_real :=
    tprod_pos_of_summable_abs_sub_one (fun i ↦ hB_toReal_pos i.2) hconv
  let cS : ℝ≥0 := ⟨cS_real, hcS_pos.le⟩
  have hcS_ne : cS ≠ 0 := ne_of_gt (show (0 : ℝ≥0) < cS from hcS_pos)
  let ν₀ : Measure (Πʳ i, [G i, B i]) := restrictedHaar B hBcompact' μ' hμ'B
  let ν : Measure (Πʳ i, [G i, B i]) := cS • ν₀
  have hν_haar : ν.IsHaarMeasure := IsHaarMeasure.nnreal_smul ν₀ hcS_ne
  have hν_box (T : Finset ι) (hST : S ⊆ T) (C : ∀ i, Set (G i))
      (hCmeas : ∀ i, MeasurableSet (C i)) (hCB : ∀ i ∉ T, C i = B i) :
      ν (box C) = (∏ i ∈ T, μ i (C i)) *
        ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) := by
    have hT_out (i : ι) (hi : i ∉ T) : IsCompact (B i : Set (G i)) ∧ μ' i (B i) = 1 :=
      ⟨hBcompact i fun hiS ↦ hi (hST hiS), hμ'B_out fun hiS ↦ hi (hST hiS)⟩
    have hν₀_C : ν₀ (box C) = ∏ i ∈ T, μ' i (C i) :=
      restrictedHaar_box B hBcompact' μ' hμ'B hT_out hCmeas hCB
    have hsplit : cS_real =
        (∏ i ∈ T \ S, (μ i (B i)).toReal) * (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) :=
      tprod_split_finset hST (fun i ↦ (μ i (B i)).toReal) (fun _ hi ↦ hB_toReal_pos hi) hconv
    have hprod_pos : 0 ≤ ∏ i ∈ T \ S, (μ i (B i)).toReal :=
      Finset.prod_nonneg fun i hi ↦ (hB_toReal_pos (Finset.mem_sdiff.mp hi).2).le
    have hcS_ennreal : (cS : ℝ≥0∞) =
        (∏ i ∈ T \ S, μ i (B i)) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) := by
      rw [← ENNReal.ofReal_coe_nnreal, show (cS : ℝ) = cS_real from rfl, hsplit,
        ENNReal.ofReal_mul hprod_pos, ENNReal.ofReal_prod_of_nonneg
          (fun i hi ↦ (hB_toReal_pos (Finset.mem_sdiff.mp hi).2).le)]
      congr 1
      refine Finset.prod_congr rfl fun i hi ↦ ?_
      exact ENNReal.ofReal_toReal (hB_lt_top (Finset.mem_sdiff.mp hi).2).ne
    have hμ'_prod : (∏ i ∈ T, μ' i (C i)) =
        (∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, ((μ i (B i))⁻¹ * μ i (C i)) := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hST]
      rw [Finset.prod_union Finset.disjoint_sdiff]
      congr 1
      · exact Finset.prod_congr rfl fun i hi ↦ by simp [μ', hi]
      · refine Finset.prod_congr rfl fun i hi ↦ ?_
        have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
        simp only [μ', hiS, ↓reduceIte]
        rw [nnreal_smul_measure_apply,
          ENNReal.coe_inv (ENNReal.toNNReal_pos (hB_pos i).ne' (hB_lt_top hiS).ne).ne',
          ENNReal.coe_toNNReal (hB_lt_top hiS).ne]
    have hcancel : (∏ i ∈ T \ S, μ i (B i)) *
        ((∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, ((μ i (B i))⁻¹ * μ i (C i))) =
          ∏ i ∈ T, μ i (C i) := by
      calc (∏ i ∈ T \ S, μ i (B i)) *
            ((∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, ((μ i (B i))⁻¹ * μ i (C i)))
          = (∏ i ∈ S, μ i (C i)) *
              ((∏ i ∈ T \ S, μ i (B i)) * ∏ i ∈ T \ S, ((μ i (B i))⁻¹ * μ i (C i))) := by ac_rfl
        _ = (∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, (μ i (B i) * ((μ i (B i))⁻¹ * μ i (C i))) := by
              rw [← Finset.prod_mul_distrib]
        _ = (∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, μ i (C i) := by
              congr 1
              refine Finset.prod_congr rfl fun i hi ↦ ?_
              have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
              rw [← mul_assoc, ENNReal.mul_inv_cancel (hB_pos i).ne' (hB_lt_top hiS).ne, one_mul]
        _ = ∏ i ∈ T, μ i (C i) := by
              rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hST]
    dsimp only [ν]
    rw [nnreal_smul_measure_apply, hν₀_C, hcS_ennreal, hμ'_prod]
    calc ((∏ i ∈ T \ S, μ i (B i)) *
            ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)) *
          ((∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, ((μ i (B i))⁻¹ * μ i (C i)))
        = ((∏ i ∈ T \ S, μ i (B i)) *
            ((∏ i ∈ S, μ i (C i)) * ∏ i ∈ T \ S, ((μ i (B i))⁻¹ * μ i (C i)))) *
          ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) := by ac_rfl
      _ = (∏ i ∈ T, μ i (C i)) *
            ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) := by rw [hcancel]
  refine ⟨ν, ⟨hν_haar, hν_box⟩, ?_⟩
  rintro ν' ⟨hν'_haar, hν'_box⟩
  choose K₀ hK₀_comp hK₀_closed hK₀_nhds using fun i : ι ↦
    exists_isCompact_isClosed_mem_nhds_one (H := G i)
  let C : ∀ i, Set (G i) := fun i ↦ if i ∈ S then K₀ i else (B i : Set (G i))
  have hCmeas (i : ι) : MeasurableSet (C i) := by
    by_cases hi : i ∈ S
    · simpa [C, hi] using (hK₀_closed i).measurableSet
    · simpa [C, hi] using (hBopen.out i).measurableSet
  have hCB (i : ι) (hi : i ∉ S) : C i = B i := by simp [C, hi]
  have hνC_pos : 0 < ν (box C) := by
    rw [hν_box S Finset.Subset.rfl C hCmeas hCB]
    refine ENNReal.mul_pos ?_ (ENNReal.ofReal_pos.mpr hcS_pos).ne'
    refine (CanonicallyOrderedAdd.prod_pos.mpr fun i hi ↦ ?_).ne'
    simp only [C, hi, ↓reduceIte]
    exact (isOpen_interior.measure_pos (μ i)
      ⟨1, mem_interior_iff_mem_nhds.mpr (hK₀_nhds i)⟩).trans_le (measure_mono interior_subset)
  have hνC_lt : ν (box C) < ⊤ := by
    rw [hν_box S Finset.Subset.rfl C hCmeas hCB]
    refine ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top
    refine ENNReal.prod_lt_top fun i hi ↦ ?_
    simp only [C, hi, ↓reduceIte]
    exact (hK₀_comp i).measure_lt_top
  exact isMulLeftInvariant_eq_of_apply_eq ν' ν hνC_pos.ne' hνC_lt.ne
    ((hν'_box S Finset.Subset.rfl C hCmeas hCB).trans
      (hν_box S Finset.Subset.rfl C hCmeas hCB).symm)

/-- The canonical convergent restricted Haar product measure on `Πʳ i, [G i, B i]` attached to local
Haar measures `μ i` whose integral masses converge absolutely outside `S`. -/
@[to_additive /-- The canonical convergent restricted additive Haar product measure on
`Πʳ i, [G i, B i]` attached to local additive Haar measures `μ i` whose integral masses converge
absolutely outside `S`. -/]
def convergentHaarProduct (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    Measure (Πʳ i, [G i, B i]) :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose

/-- `convergentHaarProduct` is a left Haar measure on `Πʳ i, [G i, B i]`. -/
@[to_additive /-- `convergentAddHaarProduct` is a left-invariant additive Haar measure on
`Πʳ i, [G i, B i]`. -/]
instance isHaarMeasure_convergentHaarProduct (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    (convergentHaarProduct B S hBcompact μ hconv).IsHaarMeasure :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose_spec.1.1

/-- Value of `convergentHaarProduct` on any measurable coordinate box `box C` agreeing with `B i`
outside a finite set `T ⊇ S`. -/
@[to_additive /-- Value of `convergentAddHaarProduct` on any measurable coordinate box `box C`
agreeing with `B i` outside a finite set `T ⊇ S`. -/]
theorem convergentHaarProduct_box (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|)
    {T : Finset ι} (hST : S ⊆ T) {C : ∀ i, Set (G i)}
    (hCmeas : ∀ i, MeasurableSet (C i)) (hCB : ∀ i ∉ T, C i = B i) :
    convergentHaarProduct B S hBcompact μ hconv (box C) =
      (∏ i ∈ T, μ i (C i)) * ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose_spec.1.2 T hST C hCmeas hCB

/-- Uniqueness of `convergentHaarProduct`: any left Haar measure satisfying the box formula above
`S` coincides with `convergentHaarProduct`. -/
@[to_additive /-- Uniqueness of `convergentAddHaarProduct`: any left-invariant additive Haar measure
satisfying the box formula above `S` coincides with `convergentAddHaarProduct`. -/]
theorem convergentHaarProduct_unique (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|)
    {ν : Measure (Πʳ i, [G i, B i])} [ν.IsHaarMeasure]
    (hν : ∀ (T : Finset ι), S ⊆ T → ∀ C : ∀ i, Set (G i),
      (∀ i, MeasurableSet (C i)) → (∀ i ∉ T, C i = B i) →
      ν (box C) = (∏ i ∈ T, μ i (C i)) *
        ENNReal.ofReal (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal)) :
    ν = convergentHaarProduct B S hBcompact μ hconv :=
  (exists_unique_convergentHaarProduct B S hBcompact μ hconv).choose_spec.2 ν ⟨inferInstance, hν⟩

/-- Enlarging the finite exceptional set `S` to `S' ⊇ S` leaves `convergentHaarProduct`
unchanged. -/
@[to_additive /-- Enlarging the finite exceptional set `S` to `S' ⊇ S` leaves
`convergentAddHaarProduct` unchanged. -/]
theorem convergentHaarProduct_of_subset (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    {S S' : Finset ι} (hSS' : S ⊆ S')
    (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (hBcompact' : ∀ i ∉ S', IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|)
    (hconv' : Summable fun i : {i // i ∉ S'} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    convergentHaarProduct B S hBcompact μ hconv =
      convergentHaarProduct B S' hBcompact' μ hconv' :=
  convergentHaarProduct_unique B S' hBcompact' μ hconv' fun _ hS'T _ hCmeas hCB ↦
    convergentHaarProduct_box B S hBcompact μ hconv (hSS'.trans hS'T) hCmeas hCB

/-- **Independence of the finite exceptional set.** The convergent restricted Haar product depends
only on `(B, μ)` and not on the choice of finite set `S` outside which compactness and convergence
are witnessed. -/
@[to_additive /-- **Independence of the finite exceptional set.** The convergent restricted additive
Haar product depends only on `(B, μ)` and not on the choice of finite set `S` outside which
compactness and convergence are witnessed. -/]
theorem convergentHaarProduct_congr_finset (B : ∀ i, K i) [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S S' : Finset ι)
    (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (hBcompact' : ∀ i ∉ S', IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|)
    (hconv' : Summable fun i : {i // i ∉ S'} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    convergentHaarProduct B S hBcompact μ hconv =
      convergentHaarProduct B S' hBcompact' μ hconv' := by
  classical
  let U : Finset ι := S ∪ S'
  have hBcompactU (i : ι) (hi : i ∉ U) : IsCompact (B i : Set (G i)) :=
    hBcompact i fun hiS ↦ hi (Finset.subset_union_left hiS)
  have hconvU : Summable fun i : {i // i ∉ U} ↦ |(μ i.1 (B i.1)).toReal - 1| :=
    summable_notMem_of_subset Finset.subset_union_left
      (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
  exact (convergentHaarProduct_of_subset B Finset.subset_union_left hBcompact hBcompactU μ
    hconv hconvU).trans
    (convergentHaarProduct_of_subset B Finset.subset_union_right hBcompact' hBcompactU μ
      hconv' hconvU).symm

/-- When `μ i (B i) = 1` cofinitely, `convergentHaarProduct` agrees with `restrictedHaar`. -/
@[to_additive /-- When `μ i (B i) = 1` cofinitely, `convergentAddHaarProduct` agrees with
`restrictedAddHaar`. -/]
theorem convergentHaarProduct_eq_restrictedHaar (B : ∀ i, K i)
    [Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (hBcompact' : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hμB : ∀ᶠ i in cofinite, μ i (B i) = 1)
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    convergentHaarProduct B S hBcompact μ hconv = restrictedHaar B hBcompact' μ hμB := by
  classical
  let S₁ : Finset ι := S ∪ (mem_cofinite.mp hμB).toFinset
  have hSS₁ : S ⊆ S₁ := Finset.subset_union_left
  have hBcompact₁ (i : ι) (hi : i ∉ S₁) : IsCompact (B i : Set (G i)) :=
    hBcompact i fun hiS ↦ hi (hSS₁ hiS)
  have hconv₁ : Summable fun i : {i // i ∉ S₁} ↦ |(μ i.1 (B i.1)).toReal - 1| :=
    summable_notMem_of_subset hSS₁ (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
  have hμB₁ (i : ι) (hi : i ∉ S₁) : μ i (B i) = 1 := by
    by_contra hnot
    exact hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
  rw [convergentHaarProduct_of_subset B hSS₁ hBcompact hBcompact₁ μ hconv hconv₁]
  symm
  refine convergentHaarProduct_unique B S₁ hBcompact₁ μ hconv₁ fun T hS₁T C hCmeas hCB ↦ ?_
  rw [restrictedHaar_box B hBcompact' μ hμB
    (fun i hiT ↦ ⟨hBcompact₁ i fun hiS₁ ↦ hiT (hS₁T hiS₁), hμB₁ i fun hiS₁ ↦ hiT (hS₁T hiS₁)⟩)
    hCmeas hCB]
  have htail : (∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal) = 1 := by
    have h1 (i : {i // i ∉ T}) : (μ i.1 (B i.1)).toReal = 1 := by
      rw [hμB₁ i.1 fun hiS₁ ↦ i.2 (hS₁T hiS₁)]
      simp
    simp_rw [h1, tprod_one]
  simp [htail]

/-- If every local Haar measure `μ i` is right-invariant, then `convergentHaarProduct` is also
right-invariant. -/
@[to_additive /-- If every local additive Haar measure `μ i` is right-translation-invariant, then
`convergentAddHaarProduct` is also right-translation-invariant. -/]
instance isMulRightInvariant_convergentHaarProduct (B : ∀ i, K i)
    [hBopen : Fact (∀ i, IsOpen (B i : Set (G i)))]
    (S : Finset ι) (hBcompact : ∀ i ∉ S, IsCompact (B i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (B i.1)).toReal - 1|) :
    (convergentHaarProduct B S hBcompact μ hconv).IsMulRightInvariant where
  map_mul_right_eq_self g := by
    classical
    have hBcompact' : ∀ᶠ i in cofinite, IsCompact (B i : Set (G i)) := by
      filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
      exact hBcompact i hi
    have _ : LocallyCompactSpace (Πʳ i, [G i, B i]) := locallyCompactSpace_of_group G hBcompact'
    set ν := convergentHaarProduct B S hBcompact μ hconv
    let T : Finset ι := S ∪ (mem_cofinite.mp g.eventually).toFinset
    have hST : S ⊆ T := Finset.subset_union_left
    have hgT (i : ι) (hi : i ∉ T) : g i ∈ B i := by
      by_contra hnot
      exact hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
    have hconvT : Summable fun i : {i // i ∉ T} ↦ |(μ i.1 (B i.1)).toReal - 1| :=
      summable_notMem_of_subset hST (fun i ↦ |(μ i (B i)).toReal - 1|) hconv
    have htail_pos : 0 < ∏' i : {i // i ∉ T}, (μ i.1 (B i.1)).toReal :=
      tprod_pos_of_summable_abs_sub_one
        (fun i ↦ ENNReal.toReal_pos
          ((hBopen.out i.1).measure_pos (μ i.1) ⟨1, one_mem (B i.1)⟩).ne'
          (hBcompact i.1 fun hiS ↦ i.2 (hST hiS)).measure_lt_top.ne) hconvT
    choose K₀ hK₀_comp hK₀_closed hK₀_nhds using fun i : ι ↦
      exists_isCompact_isClosed_mem_nhds_one (H := G i)
    let C : ∀ i, Set (G i) := fun i ↦ if i ∈ T then K₀ i else (B i : Set (G i))
    have hCmeas (i : ι) : MeasurableSet (C i) := by
      by_cases hi : i ∈ T
      · simpa [C, hi] using (hK₀_closed i).measurableSet
      · simpa [C, hi] using (hBopen.out i).measurableSet
    have hCB (i : ι) (hi : i ∉ T) : C i = B i := by simp [C, hi]
    have hνC_pos : 0 < ν (box C) := by
      rw [convergentHaarProduct_box B S hBcompact μ hconv hST hCmeas hCB]
      refine ENNReal.mul_pos (CanonicallyOrderedAdd.prod_pos.mpr fun i hi ↦ ?_).ne'
        (ENNReal.ofReal_pos.mpr htail_pos).ne'
      simp only [C, hi, ↓reduceIte]
      exact (isOpen_interior.measure_pos (μ i)
        ⟨1, mem_interior_iff_mem_nhds.mpr (hK₀_nhds i)⟩).trans_le (measure_mono interior_subset)
    have hνC_lt : ν (box C) < ⊤ := by
      rw [convergentHaarProduct_box B S hBcompact μ hconv hST hCmeas hCB]
      refine ENNReal.mul_lt_top (ENNReal.prod_lt_top fun i hi ↦ ?_) ENNReal.ofReal_lt_top
      simp only [C, hi, ↓reduceIte]
      exact (hK₀_comp i).measure_lt_top
    let C' : ∀ i, Set (G i) := fun i ↦ (· * g i) ⁻¹' C i
    have hC'meas (i : ι) : MeasurableSet (C' i) := measurable_mul_const (g i) (hCmeas i)
    have hC'B (i : ι) (hi : i ∉ T) : C' i = B i := by
      ext x
      simp only [C', mem_preimage, hCB i hi, SetLike.mem_coe]
      exact mul_mem_cancel_right (hgT i hi)
    have hpre : (· * g) ⁻¹' (box C : Set (Πʳ i, [G i, B i])) = box C' := by
      ext x
      simp [C']
    refine isMulLeftInvariant_eq_of_apply_eq (ν.map (· * g)) ν hνC_pos.ne' hνC_lt.ne ?_
    rw [map_apply (measurable_mul_const g) (measurableSet_box hCmeas), hpre,
      convergentHaarProduct_box B S hBcompact μ hconv hST hC'meas hC'B,
      convergentHaarProduct_box B S hBcompact μ hconv hST hCmeas hCB]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ measure_preimage_mul_right (μ i) (g i) (C i)

/-- **Independence of the integral model.** If two families of open subgroups `U` and `U'` agree
cofinitely, then `restrictedProductCongr U U' h` pushes `convergentHaarProduct` for `U` directly to
`convergentHaarProduct` for `U'` with no scalar factor. -/
@[to_additive map_addRestrictedProductCongr_convergentAddHaarProduct
/-- **Independence of the integral model.** If two families of open additive subgroups `U` and `U'`
agree cofinitely, then `addRestrictedProductCongr U U' h` pushes `convergentAddHaarProduct` for `U`
directly to `convergentAddHaarProduct` for `U'` with no scalar factor. -/]
theorem map_restrictedProductCongr_convergentHaarProduct
    (U U' : ∀ i, Subgroup (G i))
    [Fact (∀ i, IsOpen (U i : Set (G i)))] [Fact (∀ i, IsOpen (U' i : Set (G i)))]
    (S S' : Finset ι) (h : ∀ᶠ i in cofinite, U i = U' i)
    (hUcompact : ∀ i ∉ S, IsCompact (U i : Set (G i)))
    (hU'compact : ∀ i ∉ S', IsCompact (U' i : Set (G i)))
    (μ : ∀ i, Measure (G i)) [∀ i, (μ i).IsHaarMeasure]
    (hconv : Summable fun i : {i // i ∉ S} ↦ |(μ i.1 (U i.1)).toReal - 1|)
    (hconv' : Summable fun i : {i // i ∉ S'} ↦ |(μ i.1 (U' i.1)).toReal - 1|) :
    (convergentHaarProduct U S hUcompact μ hconv).map (restrictedProductCongr U U' h) =
      convergentHaarProduct U' S' hU'compact μ hconv' := by
  classical
  let S₀ : Finset ι := (S ∪ S') ∪ (mem_cofinite.mp h).toFinset
  have hSS₀ : S ⊆ S₀ := Finset.subset_union_left.trans Finset.subset_union_left
  have hS'S₀ : S' ⊆ S₀ := Finset.subset_union_right.trans Finset.subset_union_left
  have hUU' (i : ι) (hi : i ∉ S₀) : U i = U' i := by
    by_contra hnot
    exact hi (Finset.subset_union_right ((Set.Finite.mem_toFinset _).mpr hnot))
  have hUcompact₀ (i : ι) (hi : i ∉ S₀) : IsCompact (U i : Set (G i)) :=
    hUcompact i fun hiS ↦ hi (hSS₀ hiS)
  have hU'compact₀ (i : ι) (hi : i ∉ S₀) : IsCompact (U' i : Set (G i)) :=
    hU'compact i fun hiS' ↦ hi (hS'S₀ hiS')
  have hconv₀ : Summable fun i : {i // i ∉ S₀} ↦ |(μ i.1 (U i.1)).toReal - 1| :=
    summable_notMem_of_subset hSS₀ (fun i ↦ |(μ i (U i)).toReal - 1|) hconv
  have hconv'₀ : Summable fun i : {i // i ∉ S₀} ↦ |(μ i.1 (U' i.1)).toReal - 1| :=
    summable_notMem_of_subset hS'S₀ (fun i ↦ |(μ i (U' i)).toReal - 1|) hconv'
  rw [convergentHaarProduct_of_subset U hSS₀ hUcompact hUcompact₀ μ hconv hconv₀,
    convergentHaarProduct_of_subset U' hS'S₀ hU'compact hU'compact₀ μ hconv' hconv'₀]
  let e : (Πʳ i, [G i, (U i : Set (G i))]) ≃ₜ* (Πʳ i, [G i, (U' i : Set (G i))]) :=
    { restrictedProductCongr U U' h with
      continuous_toFun := continuous_restrictedProductCongr U U' h
      continuous_invFun := continuous_restrictedProductCongr_symm U U' h }
  have h_haar : ((convergentHaarProduct U S₀ hUcompact₀ μ hconv₀).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (convergentHaarProduct U S₀ hUcompact₀ μ hconv₀)
  have _ : ((convergentHaarProduct U S₀ hUcompact₀ μ hconv₀).map
      (restrictedProductCongr U U' h)).IsHaarMeasure := h_haar
  refine convergentHaarProduct_unique U' S₀ hU'compact₀ μ hconv'₀ fun T hS₀T C hCmeas hCU' ↦ ?_
  have hpre : (restrictedProductCongr U U' h) ⁻¹'
      (box C : Set (Πʳ i, [G i, (U' i : Set (G i))])) =
      (box C : Set (Πʳ i, [G i, (U i : Set (G i))])) := by
    ext x
    simp
  have hCU (i : ι) (hi : i ∉ T) : C i = U i := by
    rw [hCU' i hi, hUU' i fun hiS₀ ↦ hi (hS₀T hiS₀)]
  rw [map_apply (continuous_restrictedProductCongr U U' h).measurable (measurableSet_box hCmeas),
    hpre, convergentHaarProduct_box U S₀ hUcompact₀ μ hconv₀ hS₀T hCmeas hCU]
  congr 2
  refine tprod_congr fun i ↦ ?_
  rw [hUU' i.1 fun hiS₀ ↦ i.2 (hS₀T hiS₀)]

end ConvergentHaarProduct

end TauCeti
