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
  `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`, `x ⊗ ω ↦ x ω`. More generally, `D_L` and `Ω¹_cont(L/K)`
  are functorial in `F`-algebra homomorphisms (`mapAlgHom`, `mapAlgEquiv`), and in a tower
  `F → L → E` of formally étale `F`-algebras `Ω¹_cont(E/K) ≃ E ⊗_L Ω¹_cont(L/K)`
  (`mapTower`, `tensorEquivTower`).
* `d : L → Ω¹_cont(L/K)` is the universal derivation among `K`-derivations of `L` whose restriction
  to `F` is continuous for the valuation topology: for an `L`-module `M` with a Hausdorff topology
  for which scalar multiplication by `F` is continuous, a `K`-derivation `δ : L → M` factors as
  `ℓ ∘ d` with `ℓ` an `L`-linear map exactly when `δ` is continuous on `F`, and then `ℓ` is unique.
  This characterization does not use a topology on `L`.
* When `L` carries a topology, `Ω¹_cont(L/K)` carries the `L`-module topology (`continuousEquivSelf`
  when `L` is a topological semiring). When `L` is finite over `F` and carries the `F`-module
  topology, `Ω¹_cont(L/K)` also carries the `F`-module topology (`T2Space`), both `D_L` and `d`
  are continuous, every linear map out of `Ω¹_cont(L/K)` to a topological `L`-module is continuous,
  and a `K`-derivation `δ : L → M` into a Hausdorff `L`-module with continuous `L`-scalar
  multiplication is continuous on `L` if and only if it is continuous on `F`, hence if and only if
  it factors through `d`.

## Main definitions

* `TauCeti.LaurentSeries.Extension.derivation K L`: the derivation `D_L = d/dt` of `L`.
* `TauCeti.LaurentSeries.Extension.ContinuousKaehlerDifferential K L`: the continuous one-forms
  `Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.D K L`: the universal derivation `d`.
* `Extension.ContinuousKaehlerDifferential.equivSelf K L` and `continuousEquivSelf K L`: the
  `L`-linear (and continuous `L`-linear) equivalence `Ω¹_cont(L/K) ≃ L` sending `d t` to `1`.
* `Extension.ContinuousKaehlerDifferential.map K L` and `tensorEquiv K L`: the pullback
  `Ω¹_cont(F/K) → Ω¹_cont(L/K)` and `L`-linear equivalence `L ⊗_F Ω¹_cont(F/K) ≃ Ω¹_cont(L/K)`.
* `Extension.ContinuousKaehlerDifferential.mapAlgHom`, `mapAlgEquiv`, `mapTower`, and
  `tensorEquivTower`: functoriality along `F`-algebra maps and relative scalar extension in towers.
* `Extension.ContinuousKaehlerDifferential.lift`: the factorization of a derivation that is
  continuous on `F` through `d`.

## Main results

* `TauCeti.LaurentSeries.Extension.derivation_algebraMap`, `eq_derivation`,
  `derivation_algHom_apply`, `continuous_derivation`: `D_L` extends `D` uniquely, commutes with
  `F`-algebra homomorphisms, and is continuous for the `F`-module topology on finite extensions.
* `Extension.ContinuousKaehlerDifferential.map_mk` and `mapAlgHom_mk`: the pullbacks are induced by
  the maps of Kähler differentials.
* `Extension.ContinuousKaehlerDifferential.tensorEquiv_tmul` and `tensorEquivTower_tmul`: the
  scalar-extension equivalences send pure tensors to scalar multiples of pulled-back forms.
* `Extension.ContinuousKaehlerDifferential.existsUnique_compDer_eq`, `exists_compDer_eq_iff`,
  `continuous_iff_continuous_compAlgebraMap`, and `exists_compDer_eq_iff_continuous`: the algebraic
  and topological universal properties of `d`.

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

/-- In a tower `K⸨X⸩ → L → E` of formally étale `K⸨X⸩`-algebras, `D_E` extends `D_L`. -/
theorem derivation_algebraMap_tower {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] [Algebra L E]
    [IsScalarTower K⸨X⸩ L E] (x : L) :
    derivation K E (algebraMap L E x) = algebraMap L E (derivation K L x) := by
  have : IsScalarTower K L E := .of_algebraMap_smul fun c y ↦ by
    rw [IsScalarTower.algebraMap_apply K K⸨X⸩ L, algebraMap_smul, algebraMap_smul]
  have h : (derivation K E).compAlgebraMap L = (Algebra.linearMap L E).compDer (derivation K L) :=
    Derivation.eq_of_formallyUnramified (S := K⸨X⸩) fun f ↦ by
      simp [← IsScalarTower.algebraMap_apply K⸨X⸩ L E]
  exact congr($h x)

/-- Every `K⸨X⸩`-algebra homomorphism between formally étale `K⸨X⸩`-algebras intertwines their
derivations `d/dt`. -/
@[simp]
theorem derivation_algHom_apply {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] (φ : L →ₐ[K⸨X⸩] E) (x : L) :
    derivation K E (φ x) = φ (derivation K L x) := by
  let _ : Algebra L E := φ.toRingHom.toAlgebra
  have : IsScalarTower K⸨X⸩ L E := .of_algebraMap_eq' φ.comp_algebraMap.symm
  exact derivation_algebraMap_tower x

/-- **Continuity of `d/dt`.** On a finite formally étale `K⸨X⸩`-algebra carrying the `K⸨X⸩`-module
topology, the extended derivation `D_L` is continuous. -/
@[fun_prop]
theorem continuous_derivation [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L]
    [Module.Finite K⸨X⸩ L] : Continuous (derivation K L) := by
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  let b := Module.finBasis K⸨X⸩ L
  have hsum (x : L) : derivation K L x =
      ∑ i, (b.coord i x • derivation K L (b i) +
        LaurentSeries.derivative K (b.coord i x) • b i) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Module.Basis.coord_apply, Algebra.smul_def, Derivation.leibniz,
      derivation_algebraMap, laurentSeriesDerivation_apply, Algebra.algebraMap_self,
      RingHom.id_apply]
    ring
  have hterm (i : Fin (Module.finrank K⸨X⸩ L)) :
      Continuous fun x : L ↦
        b.coord i x • derivation K L (b i) + LaurentSeries.derivative K (b.coord i x) • b i := by
    have hc : Continuous (b.coord i) := IsModuleTopology.continuous_of_linearMap (b.coord i)
    have hdc : Continuous fun x : L ↦ LaurentSeries.derivative K (b.coord i x) :=
      LaurentSeries.continuous_derivative.comp hc
    exact (hc.fun_smul continuous_const).fun_add (hdc.fun_smul continuous_const)
  have hfin (s : Finset (Fin (Module.finrank K⸨X⸩ L))) :
      Continuous fun x : L ↦
        ∑ i ∈ s, (b.coord i x • derivation K L (b i) +
          LaurentSeries.derivative K (b.coord i x) • b i) := by
    induction s using Finset.cons_induction with
    | empty => simpa only [Finset.sum_empty] using continuous_const
    | cons i s hi ih => simpa only [Finset.sum_cons] using (hterm i).fun_add ih
  exact (hfin Finset.univ).congr fun x ↦ (hsum x).symm

variable (K L) in
/-- The map `x dy ↦ x * D_L y` from the Kähler differentials is surjective: `x dt ↦ x`. -/
theorem derivation_liftKaehlerDifferential_surjective :
    Function.Surjective (derivation K L).liftKaehlerDifferential :=
  fun x ↦ ⟨x • KaehlerDifferential.D K L (algebraMap K⸨X⸩ L (single 1 1)), by
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, derivation_algebraMap_single_one,
      smul_eq_mul, mul_one]⟩

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

/-- When `L` carries a topology, `Ω¹_cont(L/K)` carries the `L`-module topology. -/
noncomputable instance [TopologicalSpace L] :
    TopologicalSpace (ContinuousKaehlerDifferential K L) :=
  moduleTopology L _

instance [TopologicalSpace L] : IsModuleTopology L (ContinuousKaehlerDifferential K L) := ⟨rfl⟩

instance [TopologicalSpace L] : IsTopologicalAddGroup (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.isTopologicalAddGroup L _

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

/-! ### Functoriality and towers -/

section Functoriality

variable {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
  [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E]

/-- **Functoriality of continuous one-forms.** An `F`-algebra homomorphism `φ : L →ₐ[K⸨X⸩] E`
between formally étale `F`-algebras induces a `φ`-semilinear map
`Ω¹_cont(L/K) → Ω¹_cont(E/K)`, `x dt ↦ φ x dt`, commuting with `d`. -/
noncomputable def mapAlgHom (φ : L →ₐ[K⸨X⸩] E) :
    ContinuousKaehlerDifferential K L →ₛₗ[(φ : L →+* E)] ContinuousKaehlerDifferential K E where
  toFun ω := (equivSelf K E).symm (φ (equivSelf K L ω))
  map_add' ω η := (equivSelf K E).injective <| by simp only [map_add, LinearEquiv.apply_symm_apply]
  map_smul' x ω := (equivSelf K E).injective <| by
    simp only [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, map_mul, RingHom.coe_coe]

/-- In the frame `dt`, `mapAlgHom φ` applies `φ` to the coordinate. -/
@[simp]
theorem equivSelf_mapAlgHom (φ : L →ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K E (mapAlgHom φ ω) = φ (equivSelf K L ω) :=
  (equivSelf K E).apply_symm_apply _

/-- The semilinearity law of `mapAlgHom`, stated with `φ` applied. -/
theorem mapAlgHom_smul (φ : L →ₐ[K⸨X⸩] E) (x : L) (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom φ (x • ω) = φ x • mapAlgHom φ ω :=
  (mapAlgHom φ).map_smulₛₗ x ω

/-- `mapAlgHom φ` commutes with the universal derivations `d`. -/
@[simp]
theorem mapAlgHom_D (φ : L →ₐ[K⸨X⸩] E) (x : L) :
    mapAlgHom φ (D K L x) = D K E (φ x) :=
  (equivSelf K E).injective <| by
    rw [equivSelf_mapAlgHom, equivSelf_D, equivSelf_D, derivation_algHom_apply]

/-- On the quotient of Kähler differentials, `mapAlgHom φ` is induced by
`KaehlerDifferential.mapSemilinear`. -/
theorem mapAlgHom_mk (φ : L →ₐ[K⸨X⸩] E) (ω : Ω[L⁄K]) :
    mapAlgHom φ (mk K L ω) =
      mk K E (KaehlerDifferential.mapSemilinear (φ.restrictScalars K) ω) := by
  induction (KaehlerDifferential.span_range_derivation K L ▸ Submodule.mem_top :
      ω ∈ Submodule.span L (Set.range (KaehlerDifferential.D K L))) using
      Submodule.span_induction with
  | mem _ h =>
    obtain ⟨x, rfl⟩ := h
    rw [← D_apply, mapAlgHom_D, KaehlerDifferential.mapSemilinear_D,
      AlgHom.restrictScalars_apply, D_apply]
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add _ _ _ _ ih₁ ih₂ => rw [map_add, map_add, ih₁, ih₂, map_add, map_add]
  | smul a _ _ ih =>
    rw [LinearMap.map_smul, mapAlgHom_smul, ih, KaehlerDifferential.mapSemilinear_smul,
      AlgHom.restrictScalars_apply, LinearMap.map_smul]

/-- `mapAlgHom φ` commutes with the pullbacks from `Ω¹_cont(K⸨X⸩/K)`. -/
@[simp]
theorem mapAlgHom_map (φ : L →ₐ[K⸨X⸩] E) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapAlgHom φ (map K L ω) = map K E ω :=
  (equivSelf K E).injective <| by
    rw [equivSelf_mapAlgHom, equivSelf_map, equivSelf_map, AlgHom.commutes]

/-- Mapping along the identity fixes every continuous one-form. -/
@[simp]
theorem mapAlgHom_id (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom (AlgHom.id K⸨X⸩ L) ω = ω :=
  (equivSelf K L).injective <| by rw [equivSelf_mapAlgHom, AlgHom.id_apply]

/-- Mapping along a composite `F`-algebra homomorphism is composing the induced maps. -/
theorem mapAlgHom_comp {E' : Type*} [CommRing E'] [Algebra K⸨X⸩ E'] [Algebra K E']
    [IsScalarTower K K⸨X⸩ E'] [Algebra.FormallyEtale K⸨X⸩ E']
    (ψ : E →ₐ[K⸨X⸩] E') (φ : L →ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K L) :
    mapAlgHom (ψ.comp φ) ω = mapAlgHom ψ (mapAlgHom φ ω) :=
  (equivSelf K E').injective <| by
    rw [equivSelf_mapAlgHom, equivSelf_mapAlgHom, equivSelf_mapAlgHom, AlgHom.comp_apply]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

/-- An `F`-algebra equivalence `e : L ≃ₐ[K⸨X⸩] E` induces a semilinear equivalence on continuous
one-forms. -/
noncomputable def mapAlgEquiv (e : L ≃ₐ[K⸨X⸩] E) :
    ContinuousKaehlerDifferential K L ≃ₛₗ[(e.toRingEquiv : L →+* E)]
      ContinuousKaehlerDifferential K E where
  toFun := mapAlgHom e.toAlgHom
  invFun := mapAlgHom e.symm.toAlgHom
  map_add' := map_add _
  map_smul' x ω := by simpa using mapAlgHom_smul e.toAlgHom x ω
  left_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.symm_comp, mapAlgHom_id]
  right_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.comp_symm, mapAlgHom_id]

theorem mapAlgEquiv_apply (e : L ≃ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K L) :
    mapAlgEquiv e ω = mapAlgHom e.toAlgHom ω :=
  (rfl)

@[simp]
theorem mapAlgEquiv_symm_apply (e : L ≃ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K E) :
    (mapAlgEquiv e).symm ω = mapAlgEquiv e.symm ω :=
  (rfl)

@[simp]
theorem equivSelf_mapAlgEquiv (e : L ≃ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K E (mapAlgEquiv e ω) = e (equivSelf K L ω) :=
  equivSelf_mapAlgHom e.toAlgHom ω

@[simp]
theorem mapAlgEquiv_smul (e : L ≃ₐ[K⸨X⸩] E) (x : L) (ω : ContinuousKaehlerDifferential K L) :
    mapAlgEquiv e (x • ω) = e x • mapAlgEquiv e ω :=
  mapAlgHom_smul e.toAlgHom x ω

@[simp]
theorem mapAlgEquiv_D (e : L ≃ₐ[K⸨X⸩] E) (x : L) :
    mapAlgEquiv e (D K L x) = D K E (e x) :=
  mapAlgHom_D e.toAlgHom x

@[simp]
theorem mapAlgEquiv_map (e : L ≃ₐ[K⸨X⸩] E) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapAlgEquiv e (map K L ω) = map K E ω :=
  mapAlgHom_map e.toAlgHom ω

/-- Viewed over the base Laurent field `K⸨X⸩`, `mapAlgEquiv e` is a `K⸨X⸩`-linear equivalence. -/
noncomputable def mapLinearEquiv (e : L ≃ₐ[K⸨X⸩] E) :
    ContinuousKaehlerDifferential K L ≃ₗ[K⸨X⸩] ContinuousKaehlerDifferential K E where
  toFun := mapAlgHom e.toAlgHom
  invFun := mapAlgHom e.symm.toAlgHom
  map_add' := map_add _
  map_smul' f ω := by
    rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul L f, mapAlgHom_smul, AlgHom.commutes,
      IsScalarTower.algebraMap_smul]
  left_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.symm_comp, mapAlgHom_id]
  right_inv ω := by rw [← mapAlgHom_comp, AlgEquiv.comp_symm, mapAlgHom_id]

theorem mapLinearEquiv_apply (e : L ≃ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K L) :
    mapLinearEquiv e ω = mapAlgHom e.toAlgHom ω :=
  (rfl)

@[simp]
theorem mapLinearEquiv_symm_apply (e : L ≃ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K E) :
    (mapLinearEquiv e).symm ω = mapLinearEquiv e.symm ω :=
  (rfl)

@[simp]
theorem equivSelf_mapLinearEquiv (e : L ≃ₐ[K⸨X⸩] E) (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K E (mapLinearEquiv e ω) = e (equivSelf K L ω) :=
  equivSelf_mapAlgHom e.toAlgHom ω

@[simp]
theorem mapLinearEquiv_smul (e : L ≃ₐ[K⸨X⸩] E) (x : L) (ω : ContinuousKaehlerDifferential K L) :
    mapLinearEquiv e (x • ω) = e x • mapLinearEquiv e ω :=
  mapAlgHom_smul e.toAlgHom x ω

@[simp]
theorem mapLinearEquiv_D (e : L ≃ₐ[K⸨X⸩] E) (x : L) :
    mapLinearEquiv e (D K L x) = D K E (e x) :=
  mapAlgHom_D e.toAlgHom x

@[simp]
theorem mapLinearEquiv_map (e : L ≃ₐ[K⸨X⸩] E) (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapLinearEquiv e (map K L ω) = map K E ω :=
  mapAlgHom_map e.toAlgHom ω

variable (K L E) [Algebra L E] [IsScalarTower K⸨X⸩ L E]

/-- **Pullback in a tower.** In a tower `K⸨X⸩ → L → E` of formally étale `K⸨X⸩`-algebras, the
canonical `algebraMap L E`-semilinear pullback `Ω¹_cont(L/K) → Ω¹_cont(E/K)`. -/
noncomputable def mapTower :
    ContinuousKaehlerDifferential K L →ₛₗ[algebraMap L E] ContinuousKaehlerDifferential K E :=
  mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ L E)

/-- **Relative scalar extension in a tower.** In a tower `K⸨X⸩ → L → E` of formally étale
`K⸨X⸩`-algebras, `E ⊗_L Ω¹_cont(L/K) ≃ Ω¹_cont(E/K)` as `E`-modules. -/
noncomputable def tensorEquivTower :
    E ⊗[L] ContinuousKaehlerDifferential K L ≃ₗ[E] ContinuousKaehlerDifferential K E :=
  (AlgebraTensorModule.congr (LinearEquiv.refl E E) (equivSelf K L)).trans <|
    (AlgebraTensorModule.rid L E E).trans (equivSelf K E).symm

variable {K L E}

theorem mapTower_apply (ω : ContinuousKaehlerDifferential K L) :
    mapTower K L E ω = mapAlgHom (IsScalarTower.toAlgHom K⸨X⸩ L E) ω :=
  (rfl)

@[simp]
theorem equivSelf_mapTower (ω : ContinuousKaehlerDifferential K L) :
    equivSelf K E (mapTower K L E ω) = algebraMap L E (equivSelf K L ω) := by
  rw [mapTower_apply, equivSelf_mapAlgHom, IsScalarTower.toAlgHom_apply]

@[simp]
theorem mapTower_D (x : L) :
    mapTower K L E (D K L x) = D K E (algebraMap L E x) := by
  rw [mapTower_apply, mapAlgHom_D, IsScalarTower.toAlgHom_apply]

@[simp]
theorem mapTower_map (ω : TauCeti.ContinuousKaehlerDifferential K) :
    mapTower K L E (map K L ω) = map K E ω := by
  rw [mapTower_apply, mapAlgHom_map]

@[simp]
theorem tensorEquivTower_tmul (y : E) (ω : ContinuousKaehlerDifferential K L) :
    tensorEquivTower K L E (y ⊗ₜ ω) = y • mapTower K L E ω := by
  apply (equivSelf K E).injective
  simp [tensorEquivTower, Algebra.smul_def, mul_comm]

end Functoriality

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

/-! ### Module topology and continuous universal property -/

section Topology

variable (K L) in
/-- When `L` is a topological semiring, `equivSelf K L` is a continuous `L`-linear equivalence. -/
noncomputable def continuousEquivSelf [TopologicalSpace L] [IsTopologicalSemiring L] :
    ContinuousKaehlerDifferential K L ≃L[L] L :=
  { equivSelf K L with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (equivSelf K L).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (equivSelf K L).symm.toLinearMap }

@[simp]
theorem continuousEquivSelf_apply [TopologicalSpace L] [IsTopologicalSemiring L]
    (ω : ContinuousKaehlerDifferential K L) :
    continuousEquivSelf K L ω = equivSelf K L ω :=
  (rfl)

@[simp]
theorem continuousEquivSelf_symm_apply [TopologicalSpace L] [IsTopologicalSemiring L] (x : L) :
    (continuousEquivSelf K L).symm x = (equivSelf K L).symm x :=
  (rfl)

variable [TopologicalSpace L] [IsModuleTopology K⸨X⸩ L] [Module.Finite K⸨X⸩ L]

/-- When `L` is finite over `K⸨X⸩` and carries the `K⸨X⸩`-module topology, `Ω¹_cont(L/K)` also
carries the `K⸨X⸩`-module topology. -/
instance : IsModuleTopology K⸨X⸩ (ContinuousKaehlerDifferential K L) :=
  IsModuleTopology.restrictScalars K⸨X⸩ L _

instance : T2Space (ContinuousKaehlerDifferential K L) :=
  TauCeti.ModuleTopology.t2Space
    (Module.Free.chooseBasis K⸨X⸩ (ContinuousKaehlerDifferential K L))

@[fun_prop]
theorem continuous_equivSelf : Continuous (equivSelf K L) := by
  have := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  exact (continuousEquivSelf K L).continuous.congr fun _ ↦ rfl

/-- The universal derivation `d : L → Ω¹_cont(L/K)` is continuous for the `K⸨X⸩`-module
topology. -/
@[fun_prop]
theorem continuous_D : Continuous (D K L) := by
  have := IsModuleTopology.isTopologicalRing K⸨X⸩ L
  exact (continuousEquivSelf K L).toHomeomorph.comp_continuous_iff.mp <| by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def,
      continuousEquivSelf_apply, equivSelf_D] using continuous_derivation (K := K) (L := L)

/-- The pullback `Ω¹_cont(K⸨X⸩/K) → Ω¹_cont(L/K)` is continuous. -/
@[fun_prop]
theorem continuous_map : Continuous (map K L) :=
  IsModuleTopology.continuous_of_linearMap (map K L)

open scoped TauCeti.ModuleTopology in
variable (K L) in
/-- Under the `K⸨X⸩`-module topology on the tensor product, `tensorEquiv K L` is a continuous
`K⸨X⸩`-linear equivalence. -/
noncomputable def continuousTensorEquiv :
    L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K ≃L[K⸨X⸩]
      ContinuousKaehlerDifferential K L :=
  ((tensorEquiv K L).restrictScalars K⸨X⸩).toContinuousLinearEquivOfIsModuleTopology

open scoped TauCeti.ModuleTopology in
@[simp]
theorem continuousTensorEquiv_apply (η : L ⊗[K⸨X⸩] TauCeti.ContinuousKaehlerDifferential K) :
    continuousTensorEquiv K L η = tensorEquiv K L η := by
  simp [continuousTensorEquiv]

open scoped TauCeti.ModuleTopology in
@[simp]
theorem continuousTensorEquiv_symm_apply (ω : ContinuousKaehlerDifferential K L) :
    (continuousTensorEquiv K L).symm ω = (tensorEquiv K L).symm ω := by
  simp [continuousTensorEquiv]

/-- An algebraic `K⸨X⸩`-equivalence between finite formally étale extensions carrying the
`K⸨X⸩`-module topology induces a continuous `K⸨X⸩`-linear equivalence on continuous one-forms,
without assuming continuity of `e` in advance. -/
noncomputable def mapContinuousLinearEquiv {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] [TopologicalSpace E]
    [IsModuleTopology K⸨X⸩ E] [Module.Finite K⸨X⸩ E] (e : L ≃ₐ[K⸨X⸩] E) :
    ContinuousKaehlerDifferential K L ≃L[K⸨X⸩] ContinuousKaehlerDifferential K E :=
  (mapLinearEquiv e).toContinuousLinearEquivOfIsModuleTopology

@[simp]
theorem mapContinuousLinearEquiv_apply {E : Type*} [CommRing E] [Algebra K⸨X⸩ E] [Algebra K E]
    [IsScalarTower K K⸨X⸩ E] [Algebra.FormallyEtale K⸨X⸩ E] [TopologicalSpace E]
    [IsModuleTopology K⸨X⸩ E] [Module.Finite K⸨X⸩ E] (e : L ≃ₐ[K⸨X⸩] E)
    (ω : ContinuousKaehlerDifferential K L) :
    mapContinuousLinearEquiv e ω = mapLinearEquiv e ω := by
  simp [mapContinuousLinearEquiv]

/-- Every `L`-linear map from `Ω¹_cont(L/K)` to a module with continuous `L`-scalar multiplication
is continuous. No continuity of addition on `N` is needed. -/
@[fun_prop]
theorem continuous_of_linearMap {N : Type*} [AddCommMonoid N] [Module L N]
    [TopologicalSpace N] [ContinuousSMul L N]
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] N) : Continuous ℓ :=
  ((continuous_equivSelf (K := K) (L := L)).fun_smul continuous_const).congr fun ω ↦ by
    simpa only [map_smul] using congrArg ℓ (equivSelf_smul_D_algebraMap_single_one ω)

/-- Every derivation factoring through `d` is continuous when `L`-scalar multiplication on its
target is continuous. -/
theorem continuous_compDer {M : Type*} [AddCommGroup M] [Module L M] [Module K M]
    [IsScalarTower K L M] [TopologicalSpace M] [ContinuousSMul L M]
    (ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M) :
    Continuous (ℓ.compDer (D K L)) :=
  (continuous_of_linearMap ℓ).comp continuous_D

section TopologicalUniversalProperty

variable {M : Type*} [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
  [Module K⸨X⸩ M] [IsScalarTower K⸨X⸩ L M] [IsScalarTower K K⸨X⸩ M] [TopologicalSpace M]
  [T2Space M] [ContinuousSMul L M]

/-- The factorization `lift` of a derivation into a Hausdorff topological `L`-module is
continuous. -/
theorem continuous_lift [ContinuousSMul K⸨X⸩ M] (δ : Derivation K L M)
    (hδ : Continuous (δ.compAlgebraMap K⸨X⸩)) :
    Continuous (lift δ hδ) :=
  continuous_of_linearMap _

/-- **Continuity on `L` is determined on `K⸨X⸩`.** For a `K`-derivation `δ : L → M` into a
Hausdorff module with continuous `L`-scalar multiplication, `δ` is continuous on `L` if and only if
its restriction to `K⸨X⸩` is continuous. -/
theorem continuous_iff_continuous_compAlgebraMap (δ : Derivation K L M) :
    Continuous δ ↔ Continuous (δ.compAlgebraMap K⸨X⸩) := by
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  have : ContinuousAdd L := IsModuleTopology.toContinuousAdd K⸨X⸩ L
  refine ⟨fun hδ ↦ hδ.comp (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap K⸨X⸩ L)),
    fun hδ ↦ ?_⟩
  exact ((continuous_derivation (K := K) (L := L)).fun_smul continuous_const).congr fun x ↦
    (apply_eq_derivation_smul δ hδ x).symm

/-- **Topological universal property of `Ω¹_cont(L/K)`.** A `K`-derivation `δ : L → M` into a
Hausdorff module with continuous `L`-scalar multiplication factors through `d` if and only if `δ` is
continuous on `L`. -/
theorem exists_compDer_eq_iff_continuous (δ : Derivation K L M) :
    (∃ ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ) ↔ Continuous δ := by
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  rw [exists_compDer_eq_iff, ← continuous_iff_continuous_compAlgebraMap]

/-- Every continuous `K`-derivation `δ : L → M` into a Hausdorff module with continuous `L`-scalar
multiplication factors uniquely through `d`. -/
theorem existsUnique_compDer_eq_of_continuous (δ : Derivation K L M) (hδ : Continuous δ) :
    ∃! ℓ : ContinuousKaehlerDifferential K L →ₗ[L] M, ℓ.compDer (D K L) = δ := by
  have : ContinuousSMul K⸨X⸩ M := IsScalarTower.continuousSMul L
  exact existsUnique_compDer_eq δ ((continuous_iff_continuous_compAlgebraMap δ).mp hδ)

end TopologicalUniversalProperty

end Topology

end ContinuousKaehlerDifferential

end TauCeti.LaurentSeries.Extension
