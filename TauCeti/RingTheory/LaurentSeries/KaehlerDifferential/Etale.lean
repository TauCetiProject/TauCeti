/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.FormallyEtale
public import TauCeti.RingTheory.Kaehler.MapSemilinear
public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic
public import TauCeti.Topology.Algebra.Module.ModuleTopology

/-!
# Continuous one-forms of étale extensions of Laurent series

Let `K` be a field, `F = K⸨t⸩` and `L` a formally étale `F`-algebra, for instance a finite
separable field extension of `F` (`Algebra.FormallyEtale.of_isSeparable`). The formal derivative
`D = d/dt` of `F` extends uniquely to a `K`-derivation `D_L` of `L`
(`TauCeti.LaurentSeries.Extension.derivation`), by the extension of derivations along formally
étale maps (`Derivation.extendOfFormallyEtale`).

The continuous one-forms `Ω¹_cont(L/K)` are built from `D_L` exactly as `Ω¹_cont(F/K)` is built
from `D` (`TauCeti.ContinuousKaehlerDifferential`): they are the quotient of the algebraic Kähler
differentials `Ω[L⁄K]` by the kernel of the `L`-linear map `λ_L : Ω[L⁄K] → L`, `x dy ↦ x * D_L y`,
induced by `D_L`. This file shows:

* `λ_L` induces an `L`-linear equivalence `Ω¹_cont(L/K) ≃ L` sending `dt` to `1`, so every
  continuous one-form on `L` is uniquely `x dt`, and `dy = D_L y dt`.
* The pullback `Ω¹_cont(F/K) → Ω¹_cont(L/K)`, `f dg ↦ f dg`, is induced by the map
  `Ω[F⁄K] → Ω[L⁄K]` of Kähler differentials, and it extends to an `L`-linear equivalence
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`. More generally, any `F`-algebra homomorphism
  `φ : L →ₐ[F] L'` between formally étale `F`-algebras intertwines `D_L` and `D_{L'}` and induces a
  `φ`-semilinear pullback `Ω¹_cont(L/K) → Ω¹_cont(L'/K)`.
* `d : L → Ω¹_cont(L/K)` is the universal derivation among `K`-derivations of `L` whose restriction
  to `F` is continuous for the valuation topology: for an `L`-module `M` with a Hausdorff topology
  for which scalar multiplication by `F` is continuous, a `K`-derivation `δ : L → M` factors as
  `ℓ ∘ d` with `ℓ` an `L`-linear map exactly when `δ` is continuous on `F`, and then `ℓ` is unique.
* When `L` carries a topology, `Ω¹_cont(L/K)` carries the `L`-module topology; when `L` carries the
  `F`-module topology, both `D_L` and `d` are continuous without any finiteness assumption on `L`,
  a `K`-derivation into a Hausdorff topological `L`-module is continuous on `L` if and only if it
  is continuous on `F`, and when `L` is also finite over `F`, `Ω¹_cont(L/K)` carries the `F`-module
  topology.

## Main definitions

* `TauCeti.LaurentSeries.Extension.derivation K L`: the derivation `D_L = d/dt` of `L`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L`: the continuous one-forms
  `Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.D K L`: the universal derivation `d`.
* `Extension.ContinuousKaehlerDifferential.equivSelf K L`: the `L`-linear equivalence
  `Ω¹_cont(L/K) ≃ L` sending `d t` to `1`, upgraded to `continuousEquivSelf K L` when `L` is a
  topological semiring.
* `Extension.ContinuousKaehlerDifferential.map K L`: the pullback `Ω¹_cont(F/K) → Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.mapSemilinear`: the semilinear pullback along an
  `F`-algebra homomorphism `L →ₐ[F] L'`.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv K L`: the `L`-linear equivalence
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.lift`: the factorization of a derivation that is
  continuous on `F` through `d`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivation_algebraMap`: `D_L` extends `D`.
* `TauCeti.LaurentSeries.Extension.eq_derivation`: `D_L` is the only derivation of `L` extending
  `D`.
* `TauCeti.LaurentSeries.Extension.derivation_algHom_apply`: `F`-algebra homomorphisms intertwine
  `D_L` and `D_{L'}`.
* `TauCeti.LaurentSeries.Extension.continuous_derivation`: `D_L` is continuous whenever `L` carries
  the `F`-module topology.
* `Extension.ContinuousKaehlerDifferential.map_mk`: the pullback is induced by the map of Kähler
  differentials.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul`: the equivalence sends `x ⊗ ω` to
  `x` times the pullback of `ω`.
* `Extension.ContinuousKaehlerDifferential.existsUnique_compDer_eq`: a derivation continuous on
  `F` factors uniquely through `d`.
* `Extension.ContinuousKaehlerDifferential.exists_compDer_eq_iff`: a derivation factors through `d`
  if and only if it is continuous on `F`.

## References

* J. Tate, *Residues of differentials on curves*, Ann. Sci. ÉNS 1 (1968), for the continuous
  differentials of a finite separable extension of a complete discretely valued field.
-/

public section

open HahnSeries TensorProduct
open scoped LaurentSeries

namespace TauCeti.LaurentSeries.Extension

variable (K : Type*) [Field K] (L : Type*) [CommRing L] [Algebra K⸨X⸩ L] [Algebra K L]
  [IsScalarTower K K⸨X⸩ L] [Algebra.FormallyEtale K⸨X⸩ L]

/-! ### The derivation `d/dt` of an étale extension -/

/-- The derivation `D_L = d/dt` of a formally étale `K⸨X⸩`-algebra `L`: the unique extension of the
formal derivative of `K⸨X⸩` (`TauCeti.LaurentSeries.Extension.eq_derivation`). -/
noncomputable def derivation : Derivation K L L :=
  ((Algebra.linearMap K⸨X⸩ L).compDer (laurentSeriesDerivation K)).extendOfFormallyEtale L

variable {K L}

/-- The derivation `D_L` extends the formal derivative of `K⸨X⸩`. -/
@[simp]
theorem derivation_algebraMap (f : K⸨X⸩) :
    derivation K L (algebraMap K⸨X⸩ L f) =
      algebraMap K⸨X⸩ L (laurentSeriesDerivation K f) := by
  simp [derivation]

/-- `D_L t = 1`. -/
theorem derivation_algebraMap_single_one :
    derivation K L (algebraMap K⸨X⸩ L (single 1 1)) = 1 := by
  simp

/-- **Uniqueness of `d/dt`.** The derivation `D_L` is the only `K`-derivation of `L` extending the
formal derivative of `K⸨X⸩`. -/
theorem eq_derivation {δ : Derivation K L L}
    (h : ∀ f : K⸨X⸩, δ (algebraMap K⸨X⸩ L f) = algebraMap K⸨X⸩ L (laurentSeriesDerivation K f)) :
    δ = derivation K L :=
  Derivation.eq_extendOfFormallyEtale _ h

variable (K L) in
/-- The map `x dy ↦ x * D_L y` from the Kähler differentials is surjective: `x dt ↦ x`. -/
theorem derivation_liftKaehlerDifferential_surjective :
    Function.Surjective (derivation K L).liftKaehlerDifferential :=
  fun x ↦ ⟨x • KaehlerDifferential.D K L (algebraMap K⸨X⸩ L (single 1 1)), by
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, derivation_algebraMap_single_one,
      smul_eq_mul, mul_one]⟩

/-- Any `K⸨X⸩`-algebra homomorphism between formally étale `K⸨X⸩`-algebras intertwines their
canonical derivations `d/dt`. -/
theorem derivation_algHom_apply {L' : Type*} [CommRing L'] [Algebra K⸨X⸩ L'] [Algebra K L']
    [IsScalarTower K K⸨X⸩ L'] [Algebra.FormallyEtale K⸨X⸩ L'] (φ : L →ₐ[K⸨X⸩] L') (x : L) :
    derivation K L' (φ x) = φ (derivation K L x) :=
  Derivation.algHom_apply_eq_of_formallyUnramified φ
    (fun f ↦ by rw [derivation_algebraMap, derivation_algebraMap, φ.commutes]) x

/-- In a tower of formally étale `K⸨X⸩`-algebras `L → L'`, the derivation `d/dt` of `L'` extends
that of `L`. -/
theorem derivation_algebraMap_tower {L' : Type*} [CommRing L'] [Algebra K⸨X⸩ L'] [Algebra K L']
    [IsScalarTower K K⸨X⸩ L'] [Algebra L L'] [IsScalarTower K⸨X⸩ L L']
    [Algebra.FormallyEtale K⸨X⸩ L'] (x : L) :
    derivation K L' (algebraMap L L' x) = algebraMap L L' (derivation K L x) :=
  derivation_algHom_apply (IsScalarTower.toAlgHom K⸨X⸩ L L') x

variable (K L) in
/-- **Continuity of `d/dt` on an étale extension.** When `L` carries the `K⸨X⸩`-module topology,
`derivation K L` is continuous. -/
theorem continuous_derivation [τ₀ : TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] :
    Continuous (derivation K L) := by
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  let φ : L → L × L := fun x ↦ (x, derivation K L x)
  have hadd : @ContinuousAdd L (.induced φ inferInstance) _ := by
    refine @ContinuousAdd.mk L (.induced φ inferInstance) _ ?_
    rw [@continuous_iff_le_induced]
    let H : (L × L) × (L × L) → L × L := fun q ↦ (q.1.1 + q.2.1, q.1.2 + q.2.2)
    have hH : Continuous H := by fun_prop
    have heq : (φ ∘ fun p : L × L ↦ p.1 + p.2) = H ∘ fun p : L × L ↦ (φ p.1, φ p.2) := by
      ext <;> simp [φ, H]
    rw [prod_induced_induced φ φ, induced_compose, heq, ← induced_compose]
    exact induced_mono hH.le_induced
  have hsmul : @ContinuousSMul K⸨X⸩ L _ _ (.induced φ inferInstance) := by
    refine @ContinuousSMul.mk K⸨X⸩ L _ _ (.induced φ inferInstance) ?_
    rw [@continuous_iff_le_induced]
    have hprod : @instTopologicalSpaceProd K⸨X⸩ L inferInstance (.induced φ inferInstance) =
        instTopologicalSpaceProd.induced (fun p : K⸨X⸩ × L ↦ (p.1, φ p.2)) := by
      simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl
    let H : K⸨X⸩ × (L × L) → L × L :=
      fun q ↦ (q.1 • q.2.1, q.1 • q.2.2 + LaurentSeries.derivative K q.1 • q.2.1)
    have hD := LaurentSeries.continuous_derivative (K := K)
    have hH : Continuous H := by fun_prop
    have heq : (φ ∘ fun p : K⸨X⸩ × L ↦ p.1 • p.2) = H ∘ fun p : K⸨X⸩ × L ↦ (p.1, φ p.2) := by
      ext p <;> dsimp [φ, H]
      rw [Algebra.smul_def, (derivation K L).leibniz, derivation_algebraMap,
        laurentSeriesDerivation_apply, smul_eq_mul, smul_eq_mul, mul_comm p.2, ← Algebra.smul_def,
        ← Algebra.smul_def]
    rw [hprod, induced_compose, heq, ← induced_compose]
    exact induced_mono hH.le_induced
  exact continuous_snd.comp <| continuous_iff_le_induced.mpr <|
    (eq_moduleTopology K⸨X⸩ L).trans_le (sInf_le ⟨hsmul, hadd⟩)

/-! ### Continuous one-forms -/

variable (K L) in
/-- The **continuous one-forms** `Ω¹_cont(L/K)` of a formally étale `K⸨X⸩`-algebra `L`: the
quotient of the Kähler differentials `Ω[L⁄K]` by the kernel of the `L`-linear map
`x dy ↦ x * D_L y` induced by the derivation `D_L = d/dt` of `L`. -/
def ContinuousKaehlerDifferential : Type _ :=
  Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

namespace ContinuousKaehlerDifferential

noncomputable instance : AddCommGroup (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| AddCommGroup <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance : Module L (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module L <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance : Module K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module K⸨X⸩ <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

noncomputable instance : Module K (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| Module K <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance : IsScalarTower K⸨X⸩ L (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower K⸨X⸩ L <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance : IsScalarTower K L (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower K L <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

instance : IsScalarTower K K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  inferInstanceAs <| IsScalarTower K K⸨X⸩ <|
    Ω[L⁄K] ⧸ LinearMap.ker (derivation K L).liftKaehlerDifferential

variable (K L)

/-- The quotient map from the Kähler differentials to the continuous one-forms. -/
noncomputable def mk : Ω[L⁄K] →ₗ[L] ContinuousKaehlerDifferential K L :=
  Submodule.mkQ _

theorem mk_surjective : Function.Surjective (mk K L) :=
  Submodule.mkQ_surjective _

variable {K L} in
/-- A Kähler differential vanishes in `Ω¹_cont(L/K)` exactly when its image `Σ xᵢ * D_L yᵢ` under
the map induced by `D_L` vanishes. -/
theorem mk_eq_zero_iff {ω : Ω[L⁄K]} :
    mk K L ω = 0 ↔ (derivation K L).liftKaehlerDifferential ω = 0 :=
  Submodule.Quotient.mk_eq_zero _

/-- The universal derivation `d : L → Ω¹_cont(L/K)`. -/
noncomputable def D : Derivation K L (ContinuousKaehlerDifferential K L) :=
  (mk K L).compDer (KaehlerDifferential.D K L)

theorem D_apply (x : L) : D K L x = mk K L (KaehlerDifferential.D K L x) :=
  (rfl)

/-- **Continuous one-forms are multiples of `dt`.** The `L`-linear equivalence
`Ω¹_cont(L/K) ≃ L` induced by `D_L`, sending `x dy` to `x * D_L y` and `d t` to `1`. -/
noncomputable def equivSelf : ContinuousKaehlerDifferential K L ≃ₗ[L] L :=
  (derivation K L).liftKaehlerDifferential.quotKerEquivOfSurjective
    (derivation_liftKaehlerDifferential_surjective K L)

variable {K L}

@[simp]
theorem equivSelf_mk (ω : Ω[L⁄K]) :
    equivSelf K L (mk K L ω) = (derivation K L).liftKaehlerDifferential ω :=
  (rfl)

/-- The equivalence sends `d y` to `D_L y`. -/
@[simp]
theorem equivSelf_D (x : L) : equivSelf K L (D K L x) = derivation K L x := by
  simp [D_apply]

/-- The continuous one-form corresponding to `x` is `x dt`. -/
@[simp]
theorem equivSelf_symm_apply (x : L) :
    (equivSelf K L).symm x = x • D K L (algebraMap K⸨X⸩ L (single 1 1)) := by
  rw [LinearEquiv.symm_apply_eq, map_smul, equivSelf_D, derivation_algebraMap_single_one,
    smul_eq_mul, mul_one]

/-- Every continuous one-form is `x dt` for the unique `x = equivSelf K L ω`. -/
theorem equivSelf_smul_D_algebraMap_single_one (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K L ω • D K L (algebraMap K⸨X⸩ L (single 1 1)) = ω := by
  rw [← equivSelf_symm_apply, LinearEquiv.symm_apply_apply]

/-- **`dy = D_L y dt`.** -/
theorem derivation_smul_D_algebraMap_single_one (x : L) :
    derivation K L x • D K L (algebraMap K⸨X⸩ L (single 1 1)) = D K L x := by
  rw [← equivSelf_D, equivSelf_smul_D_algebraMap_single_one]

variable (K L) in
/-- `Ω¹_cont(L/K)` is free of rank one over `L`. -/
theorem finrank_eq_one [Nontrivial L] : Module.finrank L (ContinuousKaehlerDifferential K L) = 1 :=
  (equivSelf K L).finrank_eq.trans (Module.finrank_self L)

/-- Semilinear maps out of `Ω¹_cont(L/K)` agree as soon as they agree on `d t`. -/
@[ext]
theorem hom_ext {S N : Type*} [Semiring S] [AddCommMonoid N] [Module S N] {σ : L →+* S}
    {ℓ ℓ' : ContinuousKaehlerDifferential K L →ₛₗ[σ] N}
    (h : ℓ (D K L (algebraMap K⸨X⸩ L (single 1 1))) = ℓ' (D K L (algebraMap K⸨X⸩ L (single 1 1)))) :
    ℓ = ℓ' := by
  ext ω
  rw [← equivSelf_smul_D_algebraMap_single_one ω, map_smulₛₗ, map_smulₛₗ, h]

/-! ### Comparison with the one-forms of `K⸨X⸩` -/

variable (K L) in
/-- The **pullback of one-forms** `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)`, `f dg ↦ f dg`, read through
the rank-one normal forms: it sends `f dt` to `f dt`. It is induced by the map of Kähler
differentials (`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.map_mk`). -/
noncomputable def map :
    TauCeti.ContinuousKaehlerDifferential K →ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L :=
  (equivSelf K L).symm.toLinearMap.restrictScalars K⸨X⸩ ∘ₗ Algebra.linearMap K⸨X⸩ L ∘ₗ
    (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearMap

/-- The pullback sends `f dt` to `f dt`. -/
@[simp]
theorem equivSelf_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    equivSelf K L (map K L ω) =
      algebraMap K⸨X⸩ L (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K ω) := by
  simp [map, -equivSelf_symm_apply]

/-- The pullback sends `d g` to `d g`. -/
@[simp]
theorem map_D (g : K⸨X⸩) :
    map K L (TauCeti.ContinuousKaehlerDifferential.D K g) = D K L (algebraMap K⸨X⸩ L g) :=
  (equivSelf K L).injective <| by
    rw [equivSelf_map, equivSelf_D, derivation_algebraMap,
      TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries_D, laurentSeriesDerivation_apply]

/-- The pullback of one-forms is induced by the map `Ω[K⸨X⸩⁄K] → Ω[L⁄K]` of Kähler
differentials. -/
theorem map_mk (ω : Ω[K⸨X⸩⁄K]) :
    map K L (TauCeti.ContinuousKaehlerDifferential.mk K ω) =
      mk K L (KaehlerDifferential.map K K K⸨X⸩ L ω) := by
  have h : map K L ∘ₗ TauCeti.ContinuousKaehlerDifferential.mk K =
      (mk K L).restrictScalars K⸨X⸩ ∘ₗ KaehlerDifferential.map K K K⸨X⸩ L :=
    Derivation.liftKaehlerDifferential_unique _ _ <| Derivation.ext fun g ↦ by
      simpa [← TauCeti.ContinuousKaehlerDifferential.D_apply] using D_apply K L _
  exact congr($h ω)

/-- The pullback of one-forms is injective. -/
theorem map_injective [FaithfulSMul K⸨X⸩ L] : Function.Injective (map K L) := by
  intro ω η h
  apply (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).injective
  simpa using congr(equivSelf K L $h)

variable (K L) in
/-- **`Ω¹_cont(L/K) = L ⊗_F Ω¹_cont(F/K)`.** For a formally étale `F`-algebra `L`, `F = K⸨X⸩`, the
pullback of one-forms extends to an `L`-linear equivalence
`L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`
(`TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul`). -/
noncomputable def tensorEquiv :
    L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K ≃ₗ[L] ContinuousKaehlerDifferential K L :=
  LinearEquiv.baseChange K⸨X⸩ L _ _
      (TauCeti.ContinuousKaehlerDifferential.equivLaurentSeries K).toLinearEquiv ≪≫ₗ
    AlgebraTensorModule.rid K⸨X⸩ L L ≪≫ₗ (equivSelf K L).symm

/-- The equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)` sends `x ⊗ ω` to `x` times the pullback
of `ω`. -/
@[simp]
theorem tensorEquiv_tmul (x : L) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    tensorEquiv K L (x ⊗ₜ ω) = x • map K L ω := by
  apply (equivSelf K L).injective
  simp [tensorEquiv, LinearEquiv.baseChange, Algebra.smul_def, mul_comm]

/-! ### The universal property -/

section UniversalProperty

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
  [Module K⸨X⸩ M] [IsScalarTower K⸨X⸩ L M] [IsScalarTower K K⸨X⸩ M] [TopologicalSpace M]
  [ContinuousSMul K⸨X⸩ M]

/-- Every derivation factoring through `d` is continuous on `K⸨X⸩` when scalar multiplication by
`K⸨X⸩` on its target is continuous. -/
theorem continuous_compAlgebraMap_compDer (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) :
    Continuous ((ℓ.compDer (D K L)).compAlgebraMap K⸨X⸩) := by
  have h : (ℓ.compDer (D K L)).compAlgebraMap K⸨X⸩ =
      (ℓ.restrictScalars K⸨X⸩ ∘ₗ map K L).compDer (TauCeti.ContinuousKaehlerDifferential.D K) :=
    Derivation.ext fun g ↦ by simp
  rw [h]
  exact TauCeti.ContinuousKaehlerDifferential.continuous_compDer _

section Hausdorff

variable [T2Space M]

/-- A `K`-derivation `δ : L → M` into a Hausdorff module that is continuous on `K⸨X⸩` satisfies
`δ y = D_L y • δ t`. -/
theorem apply_eq_derivation_smul (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩))
    (x : L) : δ x = derivation K L x • δ (algebraMap K⸨X⸩ L (single 1 1)) := by
  have h : δ = (LinearMap.toSpanSingleton L M (δ (algebraMap K⸨X⸩ L (single 1 1)))).compDer
      (derivation K L) := Derivation.eq_of_formallyUnramified (S := K⸨X⸩) fun f ↦ by
    rw [Derivation.coe_comp, LinearMap.comp_apply, Derivation.coeFn_coe, derivation_algebraMap,
      LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, algebraMap_smul]
    exact (δ.compAlgebraMap K⸨X⸩).apply_eq_laurentSeriesDerivation_smul hδ f
  exact congr($h x)

/-- For a derivation `δ` continuous on `K⸨X⸩`, the map `Ω[L⁄K] → M` it induces is `λ_L` followed
by `x ↦ x • δ t`, where `λ_L` is the map induced by `D_L`. -/
theorem liftKaehlerDifferential_eq_toSpanSingleton_comp (δ : Derivation K L M)
    (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    δ.liftKaehlerDifferential = LinearMap.toSpanSingleton L M
      (δ (algebraMap K⸨X⸩ L (single 1 1))) ∘ₗ (derivation K L).liftKaehlerDifferential := by
  ext x
  simp [apply_eq_derivation_smul δ hδ x]

/-- **The factorization of a derivation through `d`.** A `K`-derivation `δ : L → M` that is
continuous on `K⸨X⸩` factors through `Ω¹_cont(L/K)`, by the `L`-linear map induced by its Kähler
lift. -/
noncomputable def lift (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    ContinuousKaehlerDifferential K L →ₗ[L] M :=
  Submodule.liftQ _ δ.liftKaehlerDifferential fun ω hω ↦ by
    rw [LinearMap.mem_ker, liftKaehlerDifferential_eq_toSpanSingleton_comp δ hδ,
      LinearMap.comp_apply, LinearMap.mem_ker.mp hω, map_zero]

@[simp]
theorem lift_mk (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) (ω : Ω[L⁄K]) :
    lift δ hδ (mk K L ω) = δ.liftKaehlerDifferential ω :=
  (rfl)

@[simp]
theorem lift_D (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) (x : L) :
    lift δ hδ (D K L x) = δ x := by
  simp [D_apply]

/-- The factorization of `δ` through `d` recovers `δ`. -/
theorem compDer_lift (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    (lift δ hδ).compDer (D K L) = δ :=
  Derivation.ext (lift_D δ hδ)

/-- The factorization of `δ` through `d` is unique. -/
theorem lift_unique (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩))
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) (h : ℓ.compDer (D K L) = δ) :
    ℓ = lift δ hδ :=
  hom_ext <| by rw [lift_D, ← h]; simp

/-- **Universal property of the continuous one-forms.** Every `K`-derivation of `L` into a
Hausdorff module that is continuous on `K⸨X⸩` factors uniquely through `d` by an `L`-linear
map. -/
theorem existsUnique_compDer_eq (δ : Derivation K L M) (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ :=
  ⟨lift δ hδ, compDer_lift δ hδ, fun ℓ h ↦ lift_unique δ hδ ℓ h⟩

/-- A `K`-derivation of `L` into a Hausdorff module factors through `d` if and only if it is
continuous on `K⸨X⸩`. -/
theorem exists_compDer_eq_iff (δ : Derivation K L M) :
    (∃ ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ) ↔
      Continuous (δ.compAlgebraMap K⸨X⸩) :=
  ⟨fun ⟨ℓ, h⟩ ↦ h ▸ continuous_compAlgebraMap_compDer ℓ, fun hδ ↦ ⟨lift δ hδ, compDer_lift δ hδ⟩⟩

end Hausdorff

end UniversalProperty

/-! ### Functoriality along `K⸨X⸩`-algebra homomorphisms -/

section Functoriality

variable {L' L'' : Type*} [CommRing L'] [Algebra K⸨X⸩ L'] [Algebra K L']
  [IsScalarTower K K⸨X⸩ L'] [Algebra.FormallyEtale K⸨X⸩ L']
  [CommRing L''] [Algebra K⸨X⸩ L''] [Algebra K L'']
  [IsScalarTower K K⸨X⸩ L''] [Algebra.FormallyEtale K⸨X⸩ L'']

/-- **Semilinear pullback of continuous one-forms** along a `K⸨X⸩`-algebra homomorphism
`φ : L →ₐ[K⸨X⸩] L'`: it sends `x dt` to `φ x dt` and `d x` to `d (φ x)`. -/
noncomputable def mapSemilinear (φ : L →ₐ[K⸨X⸩] L') :
    ContinuousKaehlerDifferential K L →ₛₗ[φ.toRingHom] ContinuousKaehlerDifferential K L' where
  toFun ω := (equivSelf K L').symm (φ (equivSelf K L ω))
  map_add' ω η := by rw [map_add, map_add, map_add]
  map_smul' x ω := by
    rw [LinearEquiv.map_smul, smul_eq_mul, map_mul, ← smul_eq_mul, LinearEquiv.map_smul]
    rfl

@[simp]
theorem equivSelf_mapSemilinear (φ : L →ₐ[K⸨X⸩] L') (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K L' (mapSemilinear φ ω) = φ (equivSelf K L ω) :=
  (equivSelf K L').apply_symm_apply _

@[simp]
theorem mapSemilinear_smul (φ : L →ₐ[K⸨X⸩] L') (x : L) (ω : ContinuousKaehlerDifferential K L) :
    mapSemilinear φ (x • ω) = φ x • mapSemilinear φ ω :=
  (mapSemilinear φ).map_smulₛₗ x ω

/-- The semilinear pullback sends `d x` to `d (φ x)`. -/
@[simp]
theorem mapSemilinear_D (φ : L →ₐ[K⸨X⸩] L') (x : L) :
    mapSemilinear φ (D K L x) = D K L' (φ x) :=
  (equivSelf K L').injective <| by
    rw [equivSelf_mapSemilinear, equivSelf_D, equivSelf_D, derivation_algHom_apply]

/-- The semilinear pullback on `Ω¹_cont` is induced by `KaehlerDifferential.mapSemilinear` on
algebraic Kähler differentials. -/
theorem mapSemilinear_mk (φ : L →ₐ[K⸨X⸩] L') (ω : Ω[L⁄K]) :
    mapSemilinear φ (mk K L ω) =
      mk K L' (KaehlerDifferential.mapSemilinear (φ.restrictScalars K) ω) := by
  have hω : ω ∈ (⊤ : Submodule L Ω[L⁄K]) := Submodule.mem_top
  rw [← KaehlerDifferential.span_range_derivation] at hω
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [← D_apply, mapSemilinear_D, KaehlerDifferential.mapSemilinear_D,
      AlgHom.restrictScalars_apply, D_apply]
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [LinearMap.map_smul, mapSemilinear_smul, hx, KaehlerDifferential.mapSemilinear_smul,
      LinearMap.map_smul, AlgHom.restrictScalars_apply]

/-- Pulling back from `K⸨X⸩` to `L` and then along `φ : L →ₐ[K⸨X⸩] L'` is pulling back directly to
`L'`. -/
@[simp]
theorem mapSemilinear_map (φ : L →ₐ[K⸨X⸩] L') (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapSemilinear φ (map K L ω) = map K L' ω :=
  (equivSelf K L').injective <| by
    rw [equivSelf_mapSemilinear, equivSelf_map, equivSelf_map, φ.commutes]

@[simp]
theorem mapSemilinear_id_apply (ω : ContinuousKaehlerDifferential K L) :
    mapSemilinear (AlgHom.id K⸨X⸩ L) ω = ω :=
  (equivSelf K L).injective <| by rw [equivSelf_mapSemilinear, AlgHom.id_apply]

theorem mapSemilinear_id :
    (mapSemilinear (AlgHom.id K⸨X⸩ L) :
      ContinuousKaehlerDifferential K L →ₗ[L] ContinuousKaehlerDifferential K L) =
      LinearMap.id :=
  LinearMap.ext mapSemilinear_id_apply

@[simp]
theorem mapSemilinear_comp_apply (ψ : L' →ₐ[K⸨X⸩] L'') (φ : L →ₐ[K⸨X⸩] L')
    (ω : ContinuousKaehlerDifferential K L) :
    mapSemilinear (ψ.comp φ) ω = mapSemilinear ψ (mapSemilinear φ ω) :=
  (equivSelf K L'').injective <| by
    rw [equivSelf_mapSemilinear, equivSelf_mapSemilinear, equivSelf_mapSemilinear,
      AlgHom.comp_apply]

theorem mapSemilinear_comp (ψ : L' →ₐ[K⸨X⸩] L'') (φ : L →ₐ[K⸨X⸩] L') :
    mapSemilinear (ψ.comp φ) = (mapSemilinear ψ).comp (mapSemilinear φ) :=
  LinearMap.ext (mapSemilinear_comp_apply ψ φ)

@[simp]
theorem mapSemilinear_apply_symm_apply (e : L ≃ₐ[K⸨X⸩] L')
    (ω : ContinuousKaehlerDifferential K L') :
    mapSemilinear e.toAlgHom (mapSemilinear e.symm.toAlgHom ω) = ω := by
  rw [← mapSemilinear_comp_apply, AlgEquiv.comp_symm, mapSemilinear_id_apply]

@[simp]
theorem mapSemilinear_symm_apply_apply (e : L ≃ₐ[K⸨X⸩] L')
    (ω : ContinuousKaehlerDifferential K L) :
    mapSemilinear e.symm.toAlgHom (mapSemilinear e.toAlgHom ω) = ω :=
  mapSemilinear_apply_symm_apply e.symm ω

/-- An isomorphism `e : L ≃ₐ[K⸨X⸩] L'` of formally étale `K⸨X⸩`-algebras induces a `K⸨X⸩`-linear
equivalence of continuous one-forms, semilinear with respect to `e`. -/
noncomputable def congrLinearEquiv (e : L ≃ₐ[K⸨X⸩] L') :
    ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩] ContinuousKaehlerDifferential K L' :=
  ((equivSelf K L).restrictScalars K⸨X⸩).trans <|
    e.toLinearEquiv.trans ((equivSelf K L').restrictScalars K⸨X⸩).symm

@[simp]
theorem congrLinearEquiv_apply (e : L ≃ₐ[K⸨X⸩] L') (ω : ContinuousKaehlerDifferential K L) :
    congrLinearEquiv e ω = mapSemilinear e.toAlgHom ω :=
  (rfl)

@[simp]
theorem congrLinearEquiv_symm (e : L ≃ₐ[K⸨X⸩] L') :
    (congrLinearEquiv (K := K) e).symm = congrLinearEquiv e.symm :=
  LinearEquiv.ext fun _ ↦ rfl

end Functoriality

/-! ### Module topology on continuous one-forms -/

section Topology

variable [TopologicalSpace L]

/-- Continuous one-forms of `L` carry the `L`-module topology. -/
noncomputable instance : TopologicalSpace (ContinuousKaehlerDifferential K L) :=
  moduleTopology L (ContinuousKaehlerDifferential K L)

instance : IsModuleTopology L (ContinuousKaehlerDifferential K L) := ⟨rfl⟩

instance : IsTopologicalAddGroup (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.isTopologicalAddGroup L _

variable (K L) in
/-- When `L` is a topological semiring, `equivSelf K L` is a continuous `L`-linear equivalence for
the `L`-module topology on `Ω¹_cont(L/K)`. -/
noncomputable def continuousEquivSelf [IsTopologicalSemiring L] :
    ContinuousKaehlerDifferential K L ≃L[L] L :=
  (equivSelf K L).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem continuousEquivSelf_apply [IsTopologicalSemiring L]
    (ω : ContinuousKaehlerDifferential K L) :
    continuousEquivSelf K L ω = equivSelf K L ω := by
  simp [continuousEquivSelf]

@[simp]
theorem continuousEquivSelf_symm_apply [IsTopologicalSemiring L] (x : L) :
    (continuousEquivSelf K L).symm x = (equivSelf K L).symm x := by
  simp [continuousEquivSelf, -equivSelf_symm_apply]

instance [IsTopologicalSemiring L] [T2Space L] : T2Space (ContinuousKaehlerDifferential K L) :=
  (continuousEquivSelf K L).toHomeomorph.isEmbedding.t2Space

instance [ContinuousSMul K⸨X⸩ L] : ContinuousSMul K⸨X⸩ (ContinuousKaehlerDifferential K L) := by
  refine ⟨?_⟩
  have h : Continuous (fun p : K⸨X⸩ × ContinuousKaehlerDifferential K L ↦
      (p.1 • (1 : L)) • p.2) := by
    fun_prop
  exact h.congr fun p ↦ by rw [Algebra.smul_def, mul_one, IsScalarTower.algebraMap_smul]

/-- Over a topological semiring `L`, every `L`-linear map out of `Ω¹_cont(L/K)` into a module with
continuous `L`-scalar multiplication is continuous, without assuming continuity of addition. -/
@[fun_prop]
theorem continuous_of_linearMap [IsTopologicalSemiring L] {N : Type*} [AddCommMonoid N] [Module L N]
    [TopologicalSpace N] [ContinuousSMul L N] (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N) :
    Continuous ℓ := by
  have h : Continuous (fun ω ↦ continuousEquivSelf K L ω •
      ℓ (D K L (algebraMap K⸨X⸩ L (single 1 1)))) :=
    (continuousEquivSelf K L).continuous.smul continuous_const
  exact h.congr fun ω ↦ by
    simpa only [continuousEquivSelf_apply, map_smul] using
      congrArg ℓ (equivSelf_smul_D_algebraMap_single_one ω)

variable (K L) in
/-- The pullback `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)` is continuous whenever `K⸨X⸩`-scalar
multiplication on `L` is continuous. -/
theorem continuous_map [ContinuousSMul K⸨X⸩ L] : Continuous (map K L) :=
  TauCeti.ContinuousKaehlerDifferential.continuous_of_linearMap (map K L)

section ModuleTopology

variable [IsModuleTopology K⸨X⸩ L]

variable (K L) in
/-- The universal derivation `d : L → Ω¹_cont(L/K)` is continuous whenever `L` carries the
`K⸨X⸩`-module topology. -/
theorem continuous_D : Continuous (D K L) :=
  ((continuous_derivation K L).smul continuous_const).congr
    fun x ↦ derivation_smul_D_algebraMap_single_one x

/-- For a formally étale `K⸨X⸩`-algebra `L` carrying the `K⸨X⸩`-module topology and a Hausdorff
topological `L`-module `N`, a `K`-derivation `δ : L → N` is continuous on `L` if and only if its
restriction to `K⸨X⸩` is continuous. -/
theorem continuous_iff_continuous_compAlgebraMap {N : Type*} [AddCommGroup N] [Module L N]
    [Module K N] [IsScalarTower K L N] [Module K⸨X⸩ N] [IsScalarTower K⸨X⸩ L N]
    [IsScalarTower K K⸨X⸩ N] [TopologicalSpace N] [ContinuousSMul L N] [T2Space N]
    (δ : Derivation K L N) :
    Continuous δ ↔ Continuous (δ.compAlgebraMap K⸨X⸩) := by
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  have halg : Continuous (algebraMap K⸨X⸩ L) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)
  have : ContinuousSMul K⸨X⸩ N :=
    ⟨((halg.comp continuous_fst).smul continuous_snd).congr fun p ↦
      IsScalarTower.algebraMap_smul L p.1 p.2⟩
  refine ⟨fun h ↦ h.comp halg, fun h ↦ ?_⟩
  exact ((continuous_derivation K L).smul continuous_const).congr
    fun x ↦ (apply_eq_derivation_smul δ h x).symm

/-- For a finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module topology, the `L`-module
topology on `Ω¹_cont(L/K)` is also its `K⸨X⸩`-module topology. -/
instance [Module.Finite K⸨X⸩ L] : IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.restrictScalars K⸨X⸩ L _

end ModuleTopology

end Topology

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension
