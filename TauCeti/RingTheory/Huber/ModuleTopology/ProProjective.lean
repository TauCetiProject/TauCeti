/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.ModuleTopology.PseudoFlat
public import TauCeti.RingTheory.Huber.ModuleTopology.RestrictedSeries
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Logic.Equiv.Nat
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Pro-projective modules and `2`-pseudoflatness of restricted series

Let `A` be a complete Hausdorff Tate ring. Kedlaya and Liu (*Relative p-adic Hodge theory, II*,
§2.4, Definition 2.4.6, Lemma 2.4.7, and Corollaries 2.4.8–2.4.9) introduce *pro-projective*
topological `A`-modules as a unified source of `2`-pseudoflat modules encompassing both finite
projective modules and algebras of restricted power and Laurent series.

In the norm-free topological setting of Huber rings, continuous projectors onto finite projective
summands without uniform splitting bounds can have unbounded open-mapping constants across degrees;
the norm-free counterpart of uniform coordinate splittings is that `B` is an `A`-linear retract of
`c₀(ℕ, A)` (`Filter.zeroAtFilterSubmodule A Filter.cofinite`). `TauCeti.Huber.IsProProjective`
records completeness, Hausdorffness, countably generated uniformity, the compatible projector
sequence `πₖ`, and the null-sequence retraction.

## Main definitions

* `TauCeti.Huber.IsProProjective`: pro-projective uniform `A`-modules (Kedlaya–Liu II,
  Definition 2.4.6).

## Main results

* `TauCeti.Huber.IsProProjective.of_uniformLinearEquiv`,
  `TauCeti.Huber.IsProProjective.of_projective`, `TauCeti.Huber.IsProProjective.prod`: permanence
  and finite projective instances.
* `TauCeti.Huber.IsProProjective.rTensor_injective` and
  `TauCeti.Huber.IsPseudoFlat.of_isProProjective`: Lemma 2.4.7 (`Tor₁` vanishing) and
  Corollary 2.4.8 (`2`-pseudoflatness).
* `TauCeti.Huber.isProProjective_restrictedMvPowerSeriesCompletion` and
  `TauCeti.Huber.isPseudoFlat_restrictedMvPowerSeriesCompletion`: Corollary 2.4.9(a).
* `TauCeti.Huber.isProProjective_restrictedLaurentSeries`,
  `TauCeti.Huber.isPseudoFlat_restrictedLaurentSeries`, and
  `TauCeti.Huber.isPseudoFlat_twoSidedRestrictedSubmodule`: Corollary 2.4.9(b) for `A⟨T, T⁻¹⟩`.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory, II: Imperfect period rings*, §2.4,
  Definition 2.4.6, Lemma 2.4.7, and Corollaries 2.4.8–2.4.9.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 5.49 and Example 6.39.
-/

public section

open Filter Topology
open scoped TensorProduct Uniformity

namespace TauCeti.Huber

universe u v

/-! ### Pro-projective modules and `2`-pseudoflatness -/

section ProProjective

/-- A uniform `A`-module `B` is *pro-projective* over `A` (Kedlaya–Liu II, Definition 2.4.6) if `B`
is complete, Hausdorff, and has countably generated uniformity, carries a compatible sequence of
continuous `A`-linear projectors `π : ℕ → B →ₗ[A] B` with finite projective images converging
pointwise to the identity, and is an `A`-linear retract of `c₀(ℕ, A)`.

In a norm-free setting, continuous projectors onto finite projective summands alone do not force
uniform coordinate-splitting bounds: over `A = ℚ_p⟨X, Y⟩`, the `c₀`-direct sum `B` of copies
`(A, ‖·‖ₖ)` (`k ≥ 1`) with `‖h‖ₖ = max(|h(p ^ k, p ^ k)|_p, p ^ (-k : ℤ) * ‖h‖_Gauss)` carries
norm-`1` finite-free truncation projectors converging pointwise to `id`, yet
`Tor₁^A(A ⧸ (X, Y), B) ≠ 0` because `Y ⊗ (X)ₖ - X ⊗ (Y)ₖ ∈ ker((X, Y) ⊗[A] B → B)` has unique
Koszul preimage `(1, 1, …) ∉ B`. Requiring `exists_nullSequence_retract` expresses uniform
coordinate splittings without choosing Banach norms. -/
structure IsProProjective (A : Type u) [CommRing A] [TopologicalSpace A] [ContinuousAdd A]
    [ContinuousConstSMul A A] (B : Type v) [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B]
    [Module A B] : Prop where
  /-- `B` is complete. -/
  completeSpace : CompleteSpace B
  /-- `B` is Hausdorff. -/
  t2Space : T2Space B
  /-- The uniformity of `B` is countably generated. -/
  isCountablyGenerated : (𝓤 B).IsCountablyGenerated
  /-- Compatible continuous `A`-linear projectors with finite projective images converging
  pointwise to the identity. -/
  exists_projectors :
    ∃ π : ℕ → B →ₗ[A] B,
      (∀ k, Continuous (π k)) ∧
      (∀ k, Module.Finite A (LinearMap.range (π k))) ∧
      (∀ k, Module.Projective A (LinearMap.range (π k))) ∧
      (∀ ⦃k l⦄, k ≤ l → π l ∘ₗ π k = π k) ∧
      (∀ b : B, Tendsto (fun k ↦ π k b) atTop (nhds b))
  /-- Uniform coordinate-splitting witness: `B` is an `A`-linear retract of `c₀(ℕ, A)`. -/
  exists_nullSequence_retract :
    ∃ (emb : B →ₗ[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ))
      (proj : Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) →ₗ[A] B),
      proj ∘ₗ emb = LinearMap.id

namespace IsProProjective

section Basic

variable {A : Type u} [CommRing A] [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul A A]
  {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]

/-- An indiscrete nontrivial uniform `A`-module is not pro-projective: a pro-projective module must
be Hausdorff. -/
theorem not_of_not_t2Space (hnot : ¬ T2Space B) : ¬ IsProProjective A B :=
  fun h ↦ hnot h.t2Space

/-- Pro-projectivity is invariant under `A`-linear equivalences that are uniform equivalences. -/
theorem of_uniformLinearEquiv {B' : Type*} [AddCommGroup B'] [UniformSpace B']
    [IsUniformAddGroup B'] [Module A B'] (e : B ≃ₗ[A] B') (he : UniformContinuous e)
    (he_symm : UniformContinuous e.symm) (hB : IsProProjective A B) : IsProProjective A B' := by
  let ue : B ≃ᵤ B' := ⟨e.toEquiv, he, he_symm⟩
  have := hB.completeSpace; have := hB.t2Space; have := hB.isCountablyGenerated
  have hcg : (𝓤 B').IsCountablyGenerated := by
    rw [← ue.symm.isUniformInducing.comap_uniformity]; exact Filter.comap.isCountablyGenerated _ _
  obtain ⟨π, hπ_cont, hπ_fin, hπ_proj, hπ_compat, hπ_lim⟩ := hB.exists_projectors
  obtain ⟨emb, proj, hretract⟩ := hB.exists_nullSequence_retract
  let π' : ℕ → B' →ₗ[A] B' := fun k ↦ e.toLinearMap ∘ₗ π k ∘ₗ e.symm.toLinearMap
  have hrange (k : ℕ) : LinearMap.range (π' k) = (LinearMap.range (π k)).map e.toLinearMap := by
    ext y; simp only [π', LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      Submodule.mem_map]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨π k (e.symm x), ⟨e.symm x, rfl⟩, hx⟩,
      fun ⟨_, ⟨x, hx⟩, hy⟩ ↦ ⟨e x, by simpa [hx] using hy⟩⟩
  refine ⟨ue.completeSpace_iff.mp inferInstance,
    .of_injective_continuous e.symm.injective he_symm.continuous, hcg,
    ⟨π', fun k ↦ he.continuous.comp ((hπ_cont k).comp he_symm.continuous),
      fun k ↦ by have := hπ_fin k; rw [hrange]; exact Module.Finite.equiv (e.submoduleMap _),
      fun k ↦ by
        have := hπ_proj k; rw [hrange]; exact Module.Projective.of_equiv (e.submoduleMap _),
      fun k l hkl ↦ LinearMap.ext fun x ↦ by
        simpa [π'] using congrArg e congr($(hπ_compat hkl) (e.symm x)),
      fun b' ↦ by
        simpa [π', Function.comp_def, e.apply_symm_apply] using
          (he.continuous.tendsto (e.symm b')).comp (hπ_lim (e.symm b'))⟩,
    ⟨emb ∘ₗ e.symm.toLinearMap, e.toLinearMap ∘ₗ proj, LinearMap.ext fun b' ↦ by
      have hb' : proj (emb (e.symm b')) = e.symm b' := congr($hretract (e.symm b'))
      simp [hb']⟩⟩

/-- **Every finite projective module (with its natural topology) over a complete Hausdorff
first-countable commutative ring is pro-projective** (Kedlaya–Liu II, Definition 2.4.6). -/
theorem of_projective {A : Type u} [CommRing A] [UniformSpace A] [IsTopologicalRing A]
    [IsUniformAddGroup A] [CompleteSpace A] [T2Space A] [FirstCountableTopology A]
    {P : Type v} [AddCommGroup P] [UniformSpace P] [IsUniformAddGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P] [IsModuleTopology A P] :
    IsProProjective A P := by
  obtain ⟨hcomp, ht2⟩ :=
    isNaturallyComplete_iff.mp (IsNaturallyComplete.of_projective (A := A) (M := P))
  have : FirstCountableTopology P := eq_moduleTopology A P ▸ firstCountableTopology_moduleTopology
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A P
  obtain ⟨emb, proj, hret⟩ := exists_retract_zeroAtFilterSubmodule_nat A A (Fin n)
  let eFin : (Fin n → A) ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (Fin n)) :=
    { toFun := fun x ↦ ⟨x, show Tendsto x _ _ by simp⟩, invFun := Subtype.val
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  refine ⟨hcomp, ht2, IsUniformAddGroup.uniformity_countably_generated,
    ⟨fun _ ↦ LinearMap.id, fun _ ↦ continuous_id,
      fun _ ↦ by rw [LinearMap.range_id]; exact Module.Finite.equiv Submodule.topEquiv.symm,
      fun _ ↦ by rw [LinearMap.range_id]; exact Module.Projective.of_equiv Submodule.topEquiv.symm,
      fun _ _ _ ↦ LinearMap.id_comp LinearMap.id, fun _ ↦ tendsto_const_nhds⟩,
    ⟨emb ∘ₗ eFin.toLinearMap ∘ₗ g, f ∘ₗ eFin.symm.toLinearMap ∘ₗ proj, LinearMap.ext fun p ↦ ?_⟩⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]
  rw [show proj (emb (eFin (g p))) = eFin (g p) from congr($hret (eFin (g p))),
    eFin.symm_apply_apply]
  exact congr($hfg p)

/-- **A binary product of pro-projective modules is pro-projective.** -/
theorem prod {B' : Type*} [AddCommGroup B'] [UniformSpace B'] [IsUniformAddGroup B']
    [Module A B'] (hB : IsProProjective A B) (hB' : IsProProjective A B') :
    IsProProjective A (B × B') := by
  have := hB.completeSpace; have := hB'.completeSpace
  have := hB.t2Space; have := hB'.t2Space
  have := hB.isCountablyGenerated; have := hB'.isCountablyGenerated
  obtain ⟨π₁, hπ₁c, hπ₁f, hπ₁p, hπ₁m, hπ₁l⟩ := hB.exists_projectors
  obtain ⟨π₂, hπ₂c, hπ₂f, hπ₂p, hπ₂m, hπ₂l⟩ := hB'.exists_projectors
  obtain ⟨i₁, r₁, hr₁⟩ := hB.exists_nullSequence_retract
  obtain ⟨i₂, r₂, hr₂⟩ := hB'.exists_nullSequence_retract
  let π : ℕ → (B × B') →ₗ[A] (B × B') := fun k ↦ (π₁ k).prodMap (π₂ k)
  have hrange (k : ℕ) :
      LinearMap.range (π k) = (LinearMap.range (π₁ k)).prod (LinearMap.range (π₂ k)) := by
    ext ⟨y₁, y₂⟩; simp [π, Submodule.mem_prod]
  let merge : (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) ×
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) →ₗ[A]
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (ℕ ⊕ ℕ)) :=
    { toFun := fun ⟨f, g⟩ ↦ ⟨Sum.elim (f : ℕ → A) (g : ℕ → A), fun U hU ↦ by
        rw [Filter.mem_map, Filter.mem_cofinite]
        refine (((Filter.mem_cofinite.mp (Filter.mem_map.mp (f.2 hU))).image Sum.inl).union
          ((Filter.mem_cofinite.mp (Filter.mem_map.mp (g.2 hU))).image Sum.inr)).subset
          fun s hs ↦ ?_
        rcases s with n | n <;> [exact Or.inl ⟨n, hs, rfl⟩; exact Or.inr ⟨n, hs, rfl⟩]⟩
      map_add' := fun _ _ ↦ Subtype.ext <| funext fun s ↦ by cases s <;> rfl
      map_smul' := fun _ _ ↦ Subtype.ext <| funext fun s ↦ by cases s <;> rfl }
  let split : Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (ℕ ⊕ ℕ)) →ₗ[A]
      (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) ×
        Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) :=
    { toFun := fun h ↦
        (⟨fun n ↦ (h : ℕ ⊕ ℕ → A) (Sum.inl n),
            Filter.Tendsto.comp h.2 Sum.inl_injective.tendsto_cofinite⟩,
          ⟨fun n ↦ (h : ℕ ⊕ ℕ → A) (Sum.inr n),
            Filter.Tendsto.comp h.2 Sum.inr_injective.tendsto_cofinite⟩)
      map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let eSum := zeroAtFilterCofiniteCongr A A Equiv.natSumNatEquivNat
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨π, fun k ↦ (hπ₁c k).prodMap (hπ₂c k),
      fun k ↦ by
        have := hπ₁f k; have := hπ₂f k; rw [hrange]; exact .equiv (Submodule.prodEquiv _ _).symm,
      fun k ↦ by
        have := hπ₁p k; have := hπ₂p k; rw [hrange]; exact .of_equiv (Submodule.prodEquiv _ _).symm,
      fun k l hkl ↦ LinearMap.ext fun ⟨b₁, b₂⟩ ↦ Prod.ext
        (by simpa [π] using congr($(hπ₁m hkl) b₁)) (by simpa [π] using congr($(hπ₂m hkl) b₂)),
      fun ⟨b₁, b₂⟩ ↦ (hπ₁l b₁).prodMk_nhds (hπ₂l b₂)⟩,
    ⟨eSum.toLinearMap ∘ₗ merge ∘ₗ i₁.prodMap i₂,
      (r₁.prodMap r₂) ∘ₗ split ∘ₗ eSum.symm.toLinearMap,
      LinearMap.ext fun ⟨b₁, b₂⟩ ↦ Prod.ext
        (by simpa [split, merge, eSum.symm_apply_apply] using congr($hr₁ b₁))
        (by simpa [split, merge, eSum.symm_apply_apply] using congr($hr₂ b₂))⟩⟩

end Basic

section PseudoFlat

/-- **Vanishing of `Tor₁` against `c₀(ℕ, A)`** (core of Kedlaya–Liu II, Lemma 2.4.7). Over a
complete Hausdorff Tate ring `A`, for any short exact sequence `0 → M →[i] N →[p] P → 0` with `N`
finite projective and `P` `2`-pseudocoherent, `i.rTensor c₀(ℕ, A)` is injective. -/
theorem rTensor_injective_zeroAtFilterSubmodule_nat {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
    {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective
      (i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ))) := by
  have hker_coh : IsPseudoCoherentOver A (LinearMap.ker p) 1 :=
    (hP : IsPseudoCoherentOver A P ((1 : ℕ∞) + 1)).ker_of_projective hp
  let eM : M ≃ₗ[A] LinearMap.ker p :=
    LinearEquiv.ofBijective (i.codRestrict (LinearMap.ker p) hexact.apply_apply_eq_zero)
      ⟨fun x y hxy ↦ hi (congrArg Subtype.val hxy), fun ⟨y, hy⟩ ↦
        let ⟨x, hx⟩ := (hexact y).mp hy; ⟨x, Subtype.ext hx⟩⟩
  have hM_coh : IsPseudoCoherentOver A M 1 := hker_coh.of_equiv eM.symm
  have : Module.FinitePresentation A M := IsPseudoCoherentOver.one_iff.mp hM_coh
  have : Module.Finite A M := hM_coh.finite
  have : Module.FinitePresentation A N :=
    IsPseudoCoherentOver.one_iff.mp (IsPseudoCoherentOver.of_projective.mono le_top)
  have hN_nc : IsNaturallyComplete A N := IsNaturallyComplete.of_projective
  have hM_nc : IsNaturallyComplete A M := hN_nc.of_injective hi
  let _ : TopologicalSpace M := moduleTopology A M; let _ : TopologicalSpace N := moduleTopology A N
  have _ : IsModuleTopology A M := ⟨rfl⟩; have _ : IsModuleTopology A N := ⟨rfl⟩
  have _ := IsModuleTopology.toContinuousAdd A M; have _ := IsModuleTopology.toContinuousAdd A N
  have _ := IsModuleTopology.toContinuousSMul A M; have _ := IsModuleTopology.toContinuousSMul A N
  have hi_cont : Continuous i := IsModuleTopology.continuous_of_linearMap i
  let S := restrictedMvPowerSeriesSubring 1 A
  have hinj_S : Function.Injective (i.rTensor S) := fun z₁ z₂ hz ↦
    (restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete (k := 1) hM_nc).injective <|
      restrictedMvPowerSeriesSubmoduleMap_injective i hi_cont.continuousAt hi <| by
        rw [restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
          restrictedMvPowerSeriesBaseChangeEquivOfNaturallyComplete_apply,
          restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont.continuousAt z₁,
          restrictedMvPowerSeriesSubmoduleMap_baseChange i hi_cont.continuousAt z₂]
        exact congrArg restrictedMvPowerSeriesBaseChange hz
  let eNat : S ≃ₗ[A] Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ) :=
    restrictedMvPowerSeriesSubringLinearEquiv 1 A ≪≫ₗ
      restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter 1 A A ≪≫ₗ
      zeroAtFilterCofiniteCongr A A (Finsupp.uniqueEquiv (0 : Fin 1))
  have hcomm : (LinearEquiv.lTensor N eNat).toLinearMap ∘ₗ i.rTensor S ∘ₗ
      (LinearEquiv.lTensor M eNat.symm).toLinearMap =
      i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) := by
    ext; simp
  rw [← hcomm]
  exact (LinearEquiv.lTensor N eNat).injective.comp
    (hinj_S.comp (LinearEquiv.lTensor M eNat.symm).injective)

/-- **Kedlaya–Liu II, Lemma 2.4.7 (`Tor₁` half).** Over a complete Hausdorff Tate ring `A`, if `B`
is a pro-projective `A`-module and `0 → M →[i] N →[p] P → 0` is a short exact sequence of
`A`-modules with `N` finite projective and `P` `2`-pseudocoherent, then
`i.rTensor B : M ⊗[A] B → N ⊗[A] B` is injective. -/
theorem rTensor_injective {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]
    (hB : IsProProjective A B) {M N P : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [Module.Finite A N] [Module.Projective A N] [AddCommGroup P] [Module A P]
    {i : M →ₗ[A] N} {p : N →ₗ[A] P} (hi : Function.Injective i) (hp : Function.Surjective p)
    (hexact : Function.Exact i p) (hP : IsPseudoCoherentOver A P 2) :
    Function.Injective (i.rTensor B) := by
  obtain ⟨emb, proj, hretract⟩ := hB.exists_nullSequence_retract
  have hli : LinearMap.lTensor M proj ∘ₗ LinearMap.lTensor M emb = LinearMap.id := by
    rw [← LinearMap.lTensor_comp, hretract, LinearMap.lTensor_id]
  have hsq : LinearMap.lTensor N emb ∘ₗ i.rTensor B =
      i.rTensor (Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter ℕ)) ∘ₗ
        LinearMap.lTensor M emb := by ext; rfl
  exact Function.Injective.of_comp (f := LinearMap.lTensor N emb) <| by
    rw [← LinearMap.coe_comp, hsq]
    exact (rTensor_injective_zeroAtFilterSubmodule_nat hi hp hexact hP).comp
      (Function.LeftInverse.injective fun z ↦ congr($hli z))

end PseudoFlat

end IsProProjective

/-- **Kedlaya–Liu II, Corollary 2.4.8.** Over a complete Hausdorff Tate ring `A`, every
pro-projective `A`-module is `2`-pseudoflat. -/
theorem IsPseudoFlat.of_isProProjective {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]
    (hB : IsProProjective A B) : IsPseudoFlat A B 2 :=
  isPseudoFlat_iff.mpr fun _ K hK ↦ hB.rTensor_injective K.injective_subtype
    (Submodule.mkQ_surjective K) (LinearMap.exact_subtype_mkQ K) hK.isPseudoCoherentOver

/-- A pro-projective module over a complete Hausdorff Tate ring is `m`-pseudoflat for every
`2 ≤ m`, and in particular `⊤`-pseudoflat. -/
theorem IsPseudoFlat.of_isProProjective_of_le {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A]
    {B : Type v} [AddCommGroup B] [UniformSpace B] [IsUniformAddGroup B] [Module A B]
    {m : ℕ∞} (hB : IsProProjective A B) (hm : 2 ≤ m) : IsPseudoFlat A B m :=
  (IsPseudoFlat.of_isProProjective hB).mono hm

end ProProjective

/-! ### Pro-projectivity and `2`-pseudoflatness of `A⟨X₁, …, Xₖ⟩` and `A⟨T, T⁻¹⟩` -/

section RestrictedProProjective

private def boxBuildSeries {k N : ℕ} {A : Type*} [CommRing A]
    (c : (Fin k → Fin (N + 1)) → A) : MvPowerSeries (Fin k) A :=
  fun ν ↦ if h : ∀ i : Fin k, ν i ≤ N then c (fun i ↦ ⟨ν i, Nat.lt_succ_of_le (h i)⟩) else 0

@[simp]
private theorem coeff_boxBuildSeries {k N : ℕ} {A : Type*} [CommRing A]
    (c : (Fin k → Fin (N + 1)) → A) (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν (boxBuildSeries c) =
      if h : ∀ i : Fin k, ν i ≤ N then c (fun i ↦ ⟨ν i, Nat.lt_succ_of_le (h i)⟩) else 0 := rfl

private theorem coe_smul_one_weight {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (a : A)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    ((a • f).1 : MvPowerSeries (Fin k) A) =
      MvPowerSeries.C a * (f : MvPowerSeries (Fin k) A) := by
  rw [Algebra.smul_def, Subring.coe_mul, algebraMap_weightedRestrictedSubring, coe_weightedC]

private theorem boxBuildSeries_mem {k N : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (c : (Fin k → Fin (N + 1)) → A) :
    boxBuildSeries c ∈
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight := by
  rw [mem_weightedRestrictedSubring, isWeightedRestricted_one_weight_iff]
  intro U hU; rw [Filter.mem_map, Filter.mem_cofinite]
  refine (Set.finite_range fun g : Fin k → Fin (N + 1) ↦
    Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1)).subset fun ν hν ↦ ?_
  simp only [Set.mem_preimage, Set.mem_compl_iff, coeff_boxBuildSeries] at hν
  by_cases h : ∀ i : Fin k, ν i ≤ N
  · exact ⟨fun i ↦ ⟨ν i, Nat.lt_succ_of_le (h i)⟩, Finsupp.ext fun i ↦ by simp⟩
  · exact absurd (by simpa [h] using mem_of_mem_nhds hU) hν

private noncomputable def toBox {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →ₗ[A]
      ((Fin k → Fin (N + 1)) → A) where
  toFun f g := MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm (fun i ↦ (g i).1))
    (f : MvPowerSeries (Fin k) A)
  map_add' _ _ := funext fun _ ↦ by simp
  map_smul' a f := funext fun g ↦ by
    change MvPowerSeries.coeff _ ((a • f).1 : MvPowerSeries (Fin k) A) = _
    rw [coe_smul_one_weight, MvPowerSeries.coeff_C_mul]; rfl

private noncomputable def fromBox {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ) :
    ((Fin k → Fin (N + 1)) → A) →ₗ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight where
  toFun c := ⟨boxBuildSeries c, boxBuildSeries_mem c⟩
  map_add' c₁ c₂ := Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
    change MvPowerSeries.coeff ν (boxBuildSeries (c₁ + c₂)) =
      MvPowerSeries.coeff ν (boxBuildSeries c₁ + boxBuildSeries c₂)
    rw [map_add, coeff_boxBuildSeries, coeff_boxBuildSeries, coeff_boxBuildSeries]
    split_ifs <;> simp
  map_smul' a c := Subtype.ext <| MvPowerSeries.ext fun ν ↦ by
    change MvPowerSeries.coeff ν (boxBuildSeries (a • c)) =
      MvPowerSeries.coeff ν ((a • (⟨boxBuildSeries c, boxBuildSeries_mem c⟩ :
        weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)).1 :
          MvPowerSeries (Fin k) A)
    rw [coe_smul_one_weight, MvPowerSeries.coeff_C_mul, coeff_boxBuildSeries, coeff_boxBuildSeries]
    split_ifs <;> simp

private noncomputable def weightedBoxTrunc {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →ₗ[A]
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  fromBox N ∘ₗ toBox N

@[simp]
private theorem coeff_weightedBoxTrunc {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] (N : ℕ)
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight)
    (ν : Fin k →₀ ℕ) :
    MvPowerSeries.coeff ν (weightedBoxTrunc N f : MvPowerSeries (Fin k) A) =
      if ∀ i : Fin k, ν i ≤ N then
        MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) else 0 := by
  change MvPowerSeries.coeff ν (boxBuildSeries (toBox N f)) = _
  rw [coeff_boxBuildSeries]; split_ifs with h
  · change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun i ↦ ν i) _ = _
    rw [show (Finsupp.equivFunOnFinite.symm fun i ↦ ν i) = ν from Finsupp.ext fun i ↦ by simp]
  · rfl

/-- **The trivial-weight restricted power-series ring is pro-projective** for every `k : ℕ` over a
complete Hausdorff nonarchimedean ring with countably generated neighbourhoods of `0`. -/
theorem isProProjective_weightedRestrictedSubring (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] :
    IsProProjective A
      (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) := by
  have : (𝓤 (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  obtain ⟨emb₀, proj₀, hretract₀⟩ := exists_retract_zeroAtFilterSubmodule_nat A A (Fin k →₀ ℕ)
  let eW : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight ≃ₗ[A]
      Filter.zeroAtFilterSubmodule (β := A) A (Filter.cofinite : Filter (Fin k →₀ ℕ)) :=
    (AlgEquiv.ofRingEquiv
      (f := RingEquiv.subringCongr (weightedRestrictedSubring_one_weight (k := k) (A := A)))
      subringCongr_one_weight_weightedC).toLinearEquiv ≪≫ₗ
      restrictedMvPowerSeriesSubringLinearEquiv k A ≪≫ₗ
      restrictedMvPowerSeriesSubmoduleEquivZeroAtFilter k A A
  have hret (N : ℕ) (c : (Fin k → Fin (N + 1)) → A) :
      toBox (k := k) (A := A) N (fromBox N c) = c := funext fun g ↦ by
    have hg : ∀ i : Fin k, (Finsupp.equivFunOnFinite.symm fun i ↦ (g i).1) i ≤ N := fun i ↦ by
      simpa using Nat.le_of_lt_succ (g i).2
    change MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun i ↦ (g i).1)
      (boxBuildSeries c) = c g
    simp only [coeff_boxBuildSeries, hg, implies_true, ↓reduceDIte]
    exact congrArg c (funext fun i ↦ Fin.ext (by simp))
  let eBox (N : ℕ) : ((Fin k → Fin (N + 1)) → A) ≃ₗ[A]
      LinearMap.range (weightedBoxTrunc (k := k) (A := A) N) :=
    LinearEquiv.ofInjective (fromBox N) (Function.LeftInverse.injective (hret N)) ≪≫ₗ
      LinearEquiv.ofEq _ _ (LinearMap.range_comp_of_range_eq_top (fromBox N)
        (LinearMap.range_eq_top.mpr fun c ↦ ⟨fromBox N c, hret N c⟩)).symm
  refine ⟨inferInstance, inferInstance, inferInstance,
    ⟨fun N ↦ weightedBoxTrunc (k := k) (A := A) N, fun N ↦ ?_,
      fun N ↦ Module.Finite.equiv (eBox N), fun N ↦ Module.Projective.of_equiv (eBox N),
      fun N M hNM ↦ ?_, fun f ↦ ?_⟩,
    ⟨emb₀ ∘ₗ eW.toLinearMap, eW.symm.toLinearMap ∘ₗ proj₀, LinearMap.ext fun x ↦ by
      have hx : proj₀ (emb₀ (eW x)) = eW x := congr($hretract₀ (eW x))
      simp [hx]⟩⟩
  · refine continuous_of_continuousAt_zero (weightedBoxTrunc (k := k) (A := A) N).toAddMonoidHom ?_
    rw [ContinuousAt, map_zero,
      (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_iff
        (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight)]
    refine fun U _ ↦ ⟨U, trivial, fun f hf ↦ ?_⟩
    rw [SetLike.mem_coe, mem_weightedNhd] at hf ⊢
    intro ν; rw [LinearMap.toAddMonoidHom_coe, coeff_weightedBoxTrunc]
    split_ifs; · exact hf ν
    · exact (weightMul (fun _ : Fin k ↦ ({1} : Set A)) ν U.toAddSubgroup).zero_mem
  · refine LinearMap.ext fun f ↦ Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_
    rw [LinearMap.comp_apply, coeff_weightedBoxTrunc, coeff_weightedBoxTrunc]
    split_ifs with hM hN hN' <;>
      first | rfl | exact absurd (fun i ↦ le_trans (hN' i) hNM) hM
  · rw [← tendsto_sub_nhds_zero_iff,
      (hasBasis_nhds_zero_weightedTopology isWeightFamily_one_weight).tendsto_right_iff]
    intro U _
    have hfU : {ν : Fin k →₀ ℕ |
        MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∉ (U : Set A)}.Finite :=
      Filter.mem_cofinite.mp <| Filter.mem_map.mp <|
        (isWeightedRestricted_one_weight_iff.mp (mem_weightedRestrictedSubring.mp f.2))
          (U.isOpen.mem_nhds U.zero_mem)
    let N₀ : ℕ := hfU.toFinset.sup fun ν ↦ Finset.univ.sup fun i ↦ ν i
    refine Filter.eventually_atTop.mpr ⟨N₀, fun N hN ↦ ?_⟩
    rw [SetLike.mem_coe, mem_weightedNhd]; intro ν
    rw [weightMul_one_weight, AddSubgroupClass.coe_sub, map_sub, coeff_weightedBoxTrunc]
    split_ifs with hbox; · simp
    have hmemU : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ U.toAddSubgroup := by
      by_contra hnotU
      refine hbox fun i ↦ ?_
      have h₁ := Finset.le_sup (f := fun j ↦ ν j) (Finset.mem_univ i)
      have h₂ := Finset.le_sup (f := fun μ : Fin k →₀ ℕ ↦ Finset.univ.sup fun j ↦ μ j)
        (hfU.mem_toFinset.mpr hnotU)
      omega
    simpa using neg_mem hmemU

/-- **Kedlaya–Liu II, Corollary 2.4.9(a) (pro-projectivity).** -/
theorem isProProjective_restrictedMvPowerSeriesCompletion (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] :
    IsProProjective A (restrictedMvPowerSeriesCompletion k A) :=
  (isProProjective_weightedRestrictedSubring k A).of_uniformLinearEquiv
    (restrictedMvPowerSeriesCompletionAlgEquiv k A).symm.toLinearEquiv
    (by rw [AlgEquiv.coe_toLinearEquiv, coe_restrictedMvPowerSeriesCompletionAlgEquiv_symm]
        exact uniformContinuous_restrictedMvPowerSeriesCompletionEquiv_symm)
    (by change UniformContinuous ⇑(restrictedMvPowerSeriesCompletionAlgEquiv k A)
        rw [coe_restrictedMvPowerSeriesCompletionAlgEquiv]
        exact uniformContinuous_restrictedMvPowerSeriesCompletionEquiv)

/-- **Kedlaya–Liu II, Corollary 2.4.9(a) (`2`-pseudoflatness).** -/
theorem isPseudoFlat_restrictedMvPowerSeriesCompletion (k : ℕ) (A : Type*) [CommRing A]
    [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A]
    [IsTateRing A] :
    IsPseudoFlat A (restrictedMvPowerSeriesCompletion k A) 2 :=
  IsPseudoFlat.of_isProProjective (isProProjective_restrictedMvPowerSeriesCompletion k A)

/-- **Kedlaya–Liu II, Corollary 2.4.9(b) (pro-projectivity).** -/
theorem isProProjective_restrictedLaurentSeries (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [CompleteSpace A] [T0Space A] [NonarchimedeanRing A]
    [(𝓝 (0 : A)).IsCountablyGenerated] :
    IsProProjective A (RestrictedLaurentSeries A) :=
  (isProProjective_weightedRestrictedSubring 1 A).of_uniformLinearEquiv
    (RestrictedLaurentSeries.toWeightedLinearEquiv A).symm
    (RestrictedLaurentSeries.uniformContinuous_toWeightedLinearEquiv_symm A)
    (RestrictedLaurentSeries.uniformContinuous_toWeightedLinearEquiv A)

/-- **Kedlaya–Liu II, Corollary 2.4.9(b) (`2`-pseudoflatness on `RestrictedLaurentSeries`).** -/
theorem isPseudoFlat_restrictedLaurentSeries (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] :
    IsPseudoFlat A (RestrictedLaurentSeries A) 2 :=
  IsPseudoFlat.of_isProProjective (isProProjective_restrictedLaurentSeries A)

/-- **Kedlaya–Liu II, Corollary 2.4.9(b) (`2`-pseudoflatness on `twoSidedRestrictedSubmodule`).** -/
theorem isPseudoFlat_twoSidedRestrictedSubmodule (A : Type*) [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T0Space A] [IsTateRing A] :
    IsPseudoFlat A (twoSidedRestrictedSubmodule A A) 2 :=
  (isPseudoFlat_restrictedLaurentSeries A).of_equiv
    (RestrictedLaurentSeries.toTwoSidedLinearEquiv A)

end RestrictedProProjective

end TauCeti.Huber
