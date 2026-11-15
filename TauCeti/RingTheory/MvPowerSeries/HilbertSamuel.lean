/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import TauCeti.Data.Finsupp.PWO
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision

import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPowerSeries.Equiv
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.MvPowerSeries.Order

/-!
# Hilbert–Samuel diagram counting and lexicographic stabilization for formal power series

Over a field `K` and a finite variable set `σ`, the formal power series ring `MvPowerSeries σ K` is
a Noetherian local ring whose maximal ideal `𝔪` is `RingHom.ker MvPowerSeries.constantCoeff`, equal
to `Ideal.span (Set.range MvPowerSeries.X)`, and whose `m`-th power `𝔪 ^ m` consists of the series
of total-degree order at least `m` (`MvPowerSeries.mem_maximalIdeal_pow_iff_le_order`).

Combining Hironaka's complementary-monomial decomposition
`MonomialOrder.quotientEquivComplementSubmodule` with the graded lexicographic order `degLex`
identifies the truncated initial diagram
`degLex.initialDiagram (I ⊔ 𝔪 ^ (ℓ + 1)) = degLex.initialDiagram I ∪ {α | ℓ < α.degree}`
(`MonomialOrder.degLex_initialDiagram_sup_maximalIdeal_pow`) and expresses every value of the
Hilbert–Samuel function as a finite complement count in `σ →₀ ℕ`:
`TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ =
  ({α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ degLex.initialDiagram I}.ncard : ℕ∞)`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries`).

Because `degLex.initialDiagram I` is upward closed in `σ →₀ ℕ`, Bierstone–Milman's well-ordering
theorem `Finsupp.isWF_toLex_ncard_setOf_degree_le_notMem` implies that the range of
`I ↦ toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) I)` is well-founded in `Lex (ℕ → ℕ∞)`
(`TauCeti.isWF_toLex_localQuotientHilbertSamuel_mvPowerSeries`). Consequently, any sequence of
ideals whose Hilbert–Samuel functions are lexicographically (or pointwise) nonincreasing stabilizes
(`TauCeti.hsLexStabilization`,
`TauCeti.exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex`,
`TauCeti.exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone`).

## Main definitions and results

* `MvPowerSeries.isLocalHom_constantCoeff`, `MvPowerSeries.maximalIdeal_eq_comap_constantCoeff`,
  `MvPowerSeries.residueFieldEquiv`: local structure and residue field of `MvPowerSeries σ R` over a
  local ring `R`.
* `MvPowerSeries.mem_span_range_X_pow_iff_forall_degree_lt`,
  `MvPowerSeries.mem_span_range_X_pow_iff_le_order`: over any commutative ring `R` and finite `σ`,
  `Ideal.span (Set.range X) ^ m` consists of power series of order at least `m`.
* `MvPowerSeries.maximalIdeal_eq_span_range_X`, `MvPowerSeries.mem_maximalIdeal_pow_iff_le_order`:
  generators and powers of the maximal ideal of `MvPowerSeries σ K` over a field `K`.
* `MonomialOrder.complementSubmoduleEquivPi`, `MonomialOrder.quotientEquivPi`,
  `MonomialOrder.length_quotient_eq_encard_compl_initialDiagram`: coordinate isomorphism between
  `MvPowerSeries σ K ⧸ I` and `(ord.initialDiagram I)ᶜ → K`, and the resulting module-length
  formula.
* `MonomialOrder.degLex_initialDiagram_sup_maximalIdeal_pow`: the `degLex` initial diagram of
  `I ⊔ 𝔪 ^ n` is `degLex.initialDiagram I ∪ {α | n ≤ α.degree}`.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`: diagram-complement formula for
  `localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ` and evaluation `(ℓ + |σ|).choose |σ|` at `⊥`.
* `TauCeti.isWF_toLex_localQuotientHilbertSamuel_mvPowerSeries`, `TauCeti.hsLexStabilization`:
  well-foundedness and lexicographic stabilization of Hilbert–Samuel functions of ideals in
  `MvPowerSeries`.

## References

* Edward Bierstone and Pierre D. Milman, *Relations among analytic functions. I*, Ann. Inst.
  Fourier (Grenoble) 37 (1987), no. 1, 187–239; *The local geometry of analytic mappings*, Dottorato
  di Ricerca in Matematica, ETS Editrice, Pisa, 1988, Theorem 5.2.1.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302, §3.
-/

public section

open IsLocalRing

namespace MvPowerSeries

section LocalRing

/-- `MvPowerSeries.constantCoeff` is a local ring homomorphism: a formal power series is a unit iff
its constant coefficient is a unit. -/
instance isLocalHom_constantCoeff {σ R : Type*} [Ring R] :
    IsLocalHom (constantCoeff : MvPowerSeries σ R →+* R) :=
  ⟨fun _ ↦ isUnit_iff_constantCoeff.mpr⟩

/-- Over a nontrivial ring `R`, no coordinate indeterminate `X i` is a unit in `MvPowerSeries σ R`.
-/
@[simp]
theorem not_isUnit_X {σ R : Type*} [Ring R] [Nontrivial R] (i : σ) :
    ¬IsUnit (X i : MvPowerSeries σ R) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero

variable {σ R : Type*} [CommRing R]

/-- Over a local ring `R`, the maximal ideal of `MvPowerSeries σ R` is the preimage of
`maximalIdeal R` under `constantCoeff`. -/
theorem maximalIdeal_eq_comap_constantCoeff [IsLocalRing R] :
    maximalIdeal (MvPowerSeries σ R) = (maximalIdeal R).comap constantCoeff :=
  (maximalIdeal_comap (constantCoeff (σ := σ) (R := R))).symm

/-- A power series over a local ring `R` lies in `maximalIdeal (MvPowerSeries σ R)` iff its
constant coefficient lies in `maximalIdeal R`. -/
theorem mem_maximalIdeal_iff_constantCoeff_mem [IsLocalRing R] {f : MvPowerSeries σ R} :
    f ∈ maximalIdeal (MvPowerSeries σ R) ↔ constantCoeff f ∈ maximalIdeal R := by
  rw [maximalIdeal_eq_comap_constantCoeff, Ideal.mem_comap]

/-- Every coordinate indeterminate `X i` belongs to `maximalIdeal (MvPowerSeries σ R)`. -/
theorem X_mem_maximalIdeal [IsLocalRing R] (i : σ) :
    (X i : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
  simp

/-- Over a local ring `R`, `ResidueField.map constantCoeff` is bijective. -/
theorem bijective_residueFieldMap_constantCoeff [IsLocalRing R] :
    Function.Bijective (ResidueField.map (constantCoeff (σ := σ) (R := R))) := by
  refine ⟨RingHom.injective _, fun x ↦ ?_⟩
  obtain ⟨r, rfl⟩ := residue_surjective x
  exact ⟨residue _ (C r), by simp⟩

/-- `constantCoeff` induces a canonical isomorphism between the residue field of `MvPowerSeries σ R`
and the residue field of `R`. -/
noncomputable def residueFieldEquiv [IsLocalRing R] :
    ResidueField (MvPowerSeries σ R) ≃+* ResidueField R :=
  RingEquiv.ofBijective _ bijective_residueFieldMap_constantCoeff

/-- `residueFieldEquiv` maps the residue class of `f` to the residue class of `constantCoeff f`. -/
@[simp]
theorem residueFieldEquiv_residue [IsLocalRing R] (f : MvPowerSeries σ R) :
    residueFieldEquiv (residue (MvPowerSeries σ R) f) = residue R (constantCoeff f) := by
  rw [residueFieldEquiv, RingEquiv.ofBijective_apply, ResidueField.map_residue]

/-- `residueFieldEquiv.symm` maps the residue class of `r : R` to the residue class of `C r`. -/
@[simp]
theorem residueFieldEquiv_symm_residue [IsLocalRing R] (r : R) :
    residueFieldEquiv.symm (residue R r) = residue (MvPowerSeries σ R) (C r) := by
  rw [RingEquiv.symm_apply_eq, residueFieldEquiv_residue, constantCoeff_C]

/-- Over a `k`-algebra `R`, `residueFieldEquiv` is a `k`-algebra isomorphism. -/
noncomputable def residueFieldAlgEquiv (k : Type*) [CommRing k] [IsLocalRing R] [Algebra k R] :
    ResidueField (MvPowerSeries σ R) ≃ₐ[k] ResidueField R where
  __ := residueFieldEquiv (σ := σ) (R := R)
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply k (MvPowerSeries σ R) (ResidueField (MvPowerSeries σ R)),
      IsScalarTower.algebraMap_apply k R (ResidueField R), ResidueField.algebraMap_eq,
      ResidueField.algebraMap_eq, MvPowerSeries.algebraMap_apply]
    exact residueFieldEquiv_residue (C (algebraMap k R c))

/-- `residueFieldAlgEquiv` agrees with `residueFieldEquiv` on elements. -/
@[simp]
theorem residueFieldAlgEquiv_apply (k : Type*) [CommRing k] [IsLocalRing R] [Algebra k R]
    (x : ResidueField (MvPowerSeries σ R)) :
    residueFieldAlgEquiv k x = residueFieldEquiv x :=
  (rfl)

/-- `(residueFieldAlgEquiv k).symm` agrees with `residueFieldEquiv.symm` on elements. -/
@[simp]
theorem residueFieldAlgEquiv_symm_apply (k : Type*) [CommRing k] [IsLocalRing R] [Algebra k R]
    (y : ResidueField R) :
    (residueFieldAlgEquiv (σ := σ) k).symm y = residueFieldEquiv.symm y :=
  (rfl)

end LocalRing

section SpanRangeXPow

/-- The image of `MvPolynomial.idealOfVars σ R` in `MvPowerSeries σ R` is the ideal generated by
all coordinate variables `MvPowerSeries.X i`. -/
theorem map_idealOfVars_eq_span_range_X {σ R : Type*} [CommSemiring R] :
    (MvPolynomial.idealOfVars σ R).map (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  rw [MvPolynomial.idealOfVars, Ideal.map_span, ← Set.range_comp]
  congr 2
  funext i
  simp [algebraMap_apply']

variable {σ R : Type*} [CommRing R] [Finite σ]

/-- For finitely many variables `σ` over a commutative ring `R`, a power series `f` belongs to the
`m`-th power of `Ideal.span (Set.range X)` iff all coefficients of total degree strictly below `m`
vanish. -/
theorem mem_span_range_X_pow_iff_forall_degree_lt {f : MvPowerSeries σ R} {m : ℕ} :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ m ↔
      ∀ α : σ →₀ ℕ, α.degree < m → coeff α f = 0 := by
  let I₀ := MvPolynomial.idealOfVars σ R
  let e := toAdicCompletionAlgEquiv σ R
  let φ : MvPowerSeries σ R →+* AdicCompletion I₀ (MvPolynomial σ R) := e
  have hcomp : φ.comp (algebraMap (MvPolynomial σ R) (MvPowerSeries σ R)) =
      algebraMap (MvPolynomial σ R) (AdicCompletion I₀ (MvPolynomial σ R)) :=
    RingHom.ext e.commutes
  have hmap : (Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ m).map φ =
      RingHom.ker (AdicCompletion.evalₐ I₀ m) := by
    rw [← map_idealOfVars_eq_span_range_X, ← Ideal.map_pow, Ideal.map_map, hcomp,
      AdicCompletion.ker_evalₐ_eq_map_pow (MvPolynomial.fg_idealOfVars σ R) m]
  have hmem : f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ m ↔
      φ f ∈ RingHom.ker (AdicCompletion.evalₐ I₀ m) := by
    rw [← hmap, ← Ideal.mem_comap (f := φ),
      Ideal.comap_map_of_bijective φ (e.bijective : Function.Bijective φ)]
  rw [hmem, RingHom.mem_ker]
  have heq : (I₀ ^ m • ⊤ : Ideal (MvPolynomial σ R)) = I₀ ^ m := by simp
  have hφf : φ f = toAdicCompletion σ R f := rfl
  have heval : AdicCompletion.evalₐ I₀ m (φ f) =
      Ideal.Quotient.mk (I₀ ^ m) (f.truncTotal m) := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ I₀ (φ f) heq.le, AdicCompletion.eval_apply, hφf,
      toAdicCompletion_apply_eq_mk_truncTotal]
    rfl
  rw [heval, Ideal.Quotient.eq_zero_iff_mem, MvPolynomial.mem_pow_idealOfVars_iff']
  exact forall₂_congr fun α hα ↦ by rw [coeff_truncTotal _ hα]

/-- For finitely many variables `σ` over a commutative ring `R`, `f` belongs to
`Ideal.span (Set.range X) ^ m` iff `(m : ℕ∞) ≤ f.order`. -/
theorem mem_span_range_X_pow_iff_le_order {f : MvPowerSeries σ R} {m : ℕ} :
    f ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ^ m ↔ (m : ℕ∞) ≤ f.order := by
  rw [mem_span_range_X_pow_iff_forall_degree_lt, le_order_iff]
  exact forall_congr' fun α ↦ imp_congr_left Nat.cast_lt.symm

/-- For finitely many variables `σ`, the kernel of `constantCoeff` on `MvPowerSeries σ R` is
`Ideal.span (Set.range X)`. -/
theorem ker_constantCoeff_eq_span_range_X :
    RingHom.ker (constantCoeff : MvPowerSeries σ R →+* R) =
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  ext f
  rw [RingHom.mem_ker, ← pow_one (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))),
    mem_span_range_X_pow_iff_forall_degree_lt]
  refine ⟨fun h0 α hα ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl : α = 0 := (Finsupp.degree_eq_zero_iff α).mp (Nat.lt_one_iff.mp hα)
    rwa [coeff_zero_eq_constantCoeff_apply]
  · rw [← coeff_zero_eq_constantCoeff_apply]
    exact h 0 (by simp)

end SpanRangeXPow

section Field

variable {σ K : Type*} [Field K]

/-- Over a field `K`, the maximal ideal of `MvPowerSeries σ K` is the kernel of `constantCoeff`. -/
theorem maximalIdeal_eq_ker_constantCoeff :
    maximalIdeal (MvPowerSeries σ K) = RingHom.ker (constantCoeff : MvPowerSeries σ K →+* K) := by
  rw [maximalIdeal_eq_comap_constantCoeff, maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]

/-- Over a field `K`, `f ∈ maximalIdeal (MvPowerSeries σ K)` iff `constantCoeff f = 0`. -/
theorem mem_maximalIdeal_iff {f : MvPowerSeries σ K} :
    f ∈ maximalIdeal (MvPowerSeries σ K) ↔ constantCoeff f = 0 := by
  rw [maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker]

/-- Over a field `K`, `algebraMap K (ResidueField (MvPowerSeries σ K))` is surjective. -/
theorem surjective_algebraMap_residueField :
    Function.Surjective (algebraMap K (ResidueField (MvPowerSeries σ K))) := by
  intro x
  obtain ⟨c, hc⟩ := residue_surjective (residueFieldEquiv x)
  refine ⟨c, ?_⟩
  rw [IsScalarTower.algebraMap_apply K (MvPowerSeries σ K) (ResidueField (MvPowerSeries σ K)),
    ResidueField.algebraMap_eq, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← residueFieldEquiv_symm_residue, hc, RingEquiv.symm_apply_apply]

/-- Every `MvPowerSeries σ K`-module has the same length over `MvPowerSeries σ K` as over `K`. -/
theorem length_eq_length_field (M : Type*) [AddCommGroup M] [Module (MvPowerSeries σ K) M]
    [Module K M] [IsScalarTower K (MvPowerSeries σ K) M] :
    Module.length (MvPowerSeries σ K) M = Module.length K M :=
  TauCeti.length_eq_length_field_of_surjective_algebraMap_residueField K
    surjective_algebraMap_residueField M

/-- Over a field `K` and finite variable set `σ`, `maximalIdeal (MvPowerSeries σ K)` is generated by
the coordinate variables `X i`. -/
theorem maximalIdeal_eq_span_range_X [Finite σ] :
    maximalIdeal (MvPowerSeries σ K) = Ideal.span (Set.range (X : σ → MvPowerSeries σ K)) := by
  rw [maximalIdeal_eq_ker_constantCoeff, ker_constantCoeff_eq_span_range_X]

/-- Over a field `K` and finite variable set `σ`, `f` belongs to `maximalIdeal (MvPowerSeries σ K)`
to the `m`-th power iff all coefficients of total degree below `m` vanish. -/
theorem mem_maximalIdeal_pow_iff_forall_degree_lt [Finite σ] {f : MvPowerSeries σ K} {m : ℕ} :
    f ∈ maximalIdeal (MvPowerSeries σ K) ^ m ↔
      ∀ α : σ →₀ ℕ, α.degree < m → coeff α f = 0 := by
  rw [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_forall_degree_lt]

/-- Over a field `K` and finite variable set `σ`, `f` belongs to
`maximalIdeal (MvPowerSeries σ K) ^ m` iff `(m : ℕ∞) ≤ f.order`. -/
theorem mem_maximalIdeal_pow_iff_le_order [Finite σ] {f : MvPowerSeries σ K} {m : ℕ} :
    f ∈ maximalIdeal (MvPowerSeries σ K) ^ m ↔ (m : ℕ∞) ≤ f.order := by
  rw [maximalIdeal_eq_span_range_X, mem_span_range_X_pow_iff_le_order]

end Field

end MvPowerSeries

namespace MonomialOrder

section ComplementEquiv

variable {σ : Type*} (ord : MonomialOrder σ)

private noncomputable def extendCompl {R : Type*} [Semiring R]
    (I : Ideal (MvPowerSeries σ R)) (g : ↑(ord.initialDiagram I)ᶜ → R) : MvPowerSeries σ R :=
  open Classical in
  fun β ↦ if h : β ∉ ord.initialDiagram I then g ⟨β, h⟩ else 0

open Classical in
private theorem coeff_extendCompl {R : Type*} [Semiring R]
    (I : Ideal (MvPowerSeries σ R)) (g : ↑(ord.initialDiagram I)ᶜ → R) (β : σ →₀ ℕ) :
    MvPowerSeries.coeff β (ord.extendCompl I g) =
      if h : β ∉ ord.initialDiagram I then g ⟨β, h⟩ else 0 :=
  (rfl)

open Classical in
/-- The `R`-submodule `ord.complementSubmodule I` of power series supported outside
`ord.initialDiagram I` is `R`-linearly isomorphic to the full function space
`↑(ord.initialDiagram I)ᶜ → R`. -/
noncomputable def complementSubmoduleEquivPi {R : Type*} [Semiring R]
    (I : Ideal (MvPowerSeries σ R)) :
    ord.complementSubmodule I ≃ₗ[R] (↑(ord.initialDiagram I)ᶜ → R) where
  toFun f α := MvPowerSeries.coeff (α : σ →₀ ℕ) (f : MvPowerSeries σ R)
  invFun g := ⟨ord.extendCompl I g, by
    rw [ord.mem_complementSubmodule_iff]
    intro β hβ hmem
    rw [MvPowerSeries.mem_support, ord.coeff_extendCompl,
      dite_eq_right (not_not.mpr hmem)] at hβ
    exact hβ rfl⟩
  map_add' f₁ f₂ := funext fun α ↦ map_add (MvPowerSeries.coeff (α : σ →₀ ℕ)) _ _
  map_smul' c f := funext fun α ↦ map_smul (MvPowerSeries.coeff (α : σ →₀ ℕ)) c _
  left_inv f := Subtype.ext <| MvPowerSeries.ext fun β ↦ by
    rw [Subtype.coe_mk, ord.coeff_extendCompl]
    by_cases h : β ∉ ord.initialDiagram I
    · exact dite_eq_left h
    · rw [dite_eq_right h]
      symm
      by_contra hne
      exact h (ord.mem_complementSubmodule_iff.mp f.2 β (MvPowerSeries.mem_support.mpr hne))
  right_inv g := funext fun ⟨α, hα⟩ ↦
    (ord.coeff_extendCompl I g α).trans (dite_eq_left hα)

/-- `complementSubmoduleEquivPi` evaluates at `α ∈ (ord.initialDiagram I)ᶜ` by reading off the
`α`-th power-series coefficient. -/
@[simp]
theorem complementSubmoduleEquivPi_apply {R : Type*} [Semiring R]
    (I : Ideal (MvPowerSeries σ R)) (f : ord.complementSubmodule I)
    (α : ↑(ord.initialDiagram I)ᶜ) :
    ord.complementSubmoduleEquivPi I f α =
      MvPowerSeries.coeff (α : σ →₀ ℕ) (f : MvPowerSeries σ R) :=
  (rfl)

open Classical in
/-- `(ord.complementSubmoduleEquivPi I).symm g` has coefficient `g ⟨β, h⟩` outside
`ord.initialDiagram I` and `0` on `ord.initialDiagram I`. -/
@[simp]
theorem coeff_complementSubmoduleEquivPi_symm {R : Type*} [Semiring R]
    (I : Ideal (MvPowerSeries σ R)) (g : ↑(ord.initialDiagram I)ᶜ → R) (β : σ →₀ ℕ) :
    MvPowerSeries.coeff β (((ord.complementSubmoduleEquivPi I).symm g : ord.complementSubmodule I) :
        MvPowerSeries σ R) =
      if h : β ∉ ord.initialDiagram I then g ⟨β, h⟩ else 0 :=
  (rfl)

/-- Over a field `K` and finite variable set `σ`, `MvPowerSeries σ K ⧸ I` is `K`-linearly
isomorphic to `↑(ord.initialDiagram I)ᶜ → K`, sending `Ideal.Quotient.mk I G` to the coefficients of
`ord.normalRemainder I G` outside `ord.initialDiagram I`. -/
noncomputable def quotientEquivPi {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPowerSeries σ K)) :
    (MvPowerSeries σ K ⧸ I) ≃ₗ[K] (↑(ord.initialDiagram I)ᶜ → K) :=
  (ord.quotientEquivComplementSubmodule I).trans (ord.complementSubmoduleEquivPi I)

/-- `ord.quotientEquivPi I` sends `Ideal.Quotient.mk I G` to the coefficients of
`ord.normalRemainder I G` outside `ord.initialDiagram I`. -/
@[simp]
theorem quotientEquivPi_mk {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPowerSeries σ K)) (G : MvPowerSeries σ K)
    (α : ↑(ord.initialDiagram I)ᶜ) :
    ord.quotientEquivPi I (Ideal.Quotient.mk I G) α =
      MvPowerSeries.coeff (α : σ →₀ ℕ) (ord.normalRemainder I G) := by
  simp [quotientEquivPi]

/-- `(ord.quotientEquivPi I).symm g` is the quotient class of the complementary-monomial series
`(ord.complementSubmoduleEquivPi I).symm g`. -/
@[simp]
theorem quotientEquivPi_symm {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPowerSeries σ K)) (g : ↑(ord.initialDiagram I)ᶜ → K) :
    (ord.quotientEquivPi I).symm g =
      Ideal.Quotient.mk I (((ord.complementSubmoduleEquivPi I).symm g : ord.complementSubmodule I) :
        MvPowerSeries σ K) := by
  simp [quotientEquivPi]

/-- Over a field `K` and finite variable set `σ`, the `MvPowerSeries σ K`-module length of
`MvPowerSeries σ K ⧸ I` equals `(ord.initialDiagram I)ᶜ.encard` for every ideal `I` and monomial
order `ord`. -/
theorem length_quotient_eq_encard_compl_initialDiagram {K : Type*} [Field K] [Finite σ]
    (I : Ideal (MvPowerSeries σ K)) :
    Module.length (MvPowerSeries σ K) (MvPowerSeries σ K ⧸ I) =
      (ord.initialDiagram I)ᶜ.encard := by
  rw [MvPowerSeries.length_eq_length_field, (ord.quotientEquivPi I).length_eq,
    Module.length_pi, Module.length_eq_one, mul_one, Set.encard]

/-- When `(ord.initialDiagram I)ᶜ` is finite, `Module.length (MvPowerSeries σ K) (_ ⧸ I)` is the
finite cardinal `(ord.initialDiagram I)ᶜ.ncard`. -/
theorem length_quotient_eq_ncard_compl_initialDiagram {K : Type*} [Field K] [Finite σ]
    {I : Ideal (MvPowerSeries σ K)} (hfin : (ord.initialDiagram I)ᶜ.Finite) :
    Module.length (MvPowerSeries σ K) (MvPowerSeries σ K ⧸ I) =
      ((ord.initialDiagram I)ᶜ.ncard : ℕ∞) := by
  rw [ord.length_quotient_eq_encard_compl_initialDiagram, ← hfin.cast_ncard_eq]

/-- Over a nontrivial commutative semiring `R`, the initial diagram of the principal monomial ideal
`(X i ^ m)` is `Set.Ici (Finsupp.single i m)`. -/
@[simp]
theorem initialDiagram_span_X_pow {R : Type*} [CommSemiring R] [Nontrivial R] (i : σ) (m : ℕ) :
    ord.initialDiagram (Ideal.span {MvPowerSeries.X i ^ m} : Ideal (MvPowerSeries σ R)) =
      Set.Ici (Finsupp.single i m) := by
  have himg : ((fun α ↦ MvPowerSeries.monomial α (1 : R)) '' {Finsupp.single i m}) =
      {MvPowerSeries.X i ^ m} := by
    simp [MvPowerSeries.X_pow_eq]
  rw [← himg, ord.initialDiagram_span_monomial, Set.biUnion_singleton]

end ComplementEquiv

section DegLexTruncation

/-- Over a nontrivial commutative ring `R` and finite linearly ordered `σ`, adjoining the `n`-th
power of the variable ideal `Ideal.span (Set.range X)` to an ideal `I` adjoins all exponents of
total degree at least `n` to `degLex.initialDiagram I`. -/
theorem degLex_initialDiagram_sup_span_range_X_pow {σ R : Type*} [CommRing R] [Nontrivial R]
    [Finite σ] [LinearOrder σ] (I : Ideal (MvPowerSeries σ R)) (n : ℕ) :
    degLex.initialDiagram
        (I ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ n) =
      degLex.initialDiagram I ∪ {α : σ →₀ ℕ | n ≤ α.degree} := by
  ext α
  simp only [Set.mem_union, Set.mem_ofPred_eq, degLex.mem_initialDiagram_iff]
  refine ⟨fun ⟨h, hh, hh0, hexp⟩ ↦ ?_, ?_⟩
  · by_cases hdeg : n ≤ α.degree
    · exact Or.inr hdeg
    · left
      replace hdeg : α.degree < n := lt_of_not_ge hdeg
      obtain ⟨f, hfI, g, hgpow, rfl⟩ := Submodule.mem_sup.mp hh
      have hg0 : ∀ β : σ →₀ ℕ, β.degree < n → MvPowerSeries.coeff β g = 0 :=
        MvPowerSeries.mem_span_range_X_pow_iff_forall_degree_lt.mp hgpow
      have hcoeff_h : MvPowerSeries.coeff α (f + g) ≠ 0 := by
        rw [← hexp]
        exact degLex.coeff_initialExp_ne_zero hh0
      have hcoeff_f : MvPowerSeries.coeff α f ≠ 0 := by
        rwa [map_add, hg0 α hdeg, add_zero] at hcoeff_h
      have hf0 : f ≠ 0 := fun h0 ↦ hcoeff_f (by simp [h0])
      refine ⟨f, hfI, hf0, degLex.initialExp_eq_of_coeff_ne_zero_of_forall_lt hcoeff_f ?_⟩
      intro β hβ
      have hβdeg : β.degree ≤ α.degree := by
        rw [degLex_lt_iff, Finsupp.DegLex.lt_iff] at hβ
        rcases hβ with hlt | ⟨heq, _⟩
        · exact hlt.le
        · exact heq.le
      have hcoeff_hβ : MvPowerSeries.coeff β (f + g) = 0 :=
        degLex.coeff_eq_zero_of_lt_initialExp (hexp.symm ▸ hβ)
      rw [map_add, hg0 β (hβdeg.trans_lt hdeg), add_zero] at hcoeff_hβ
      exact hcoeff_hβ
  · rintro (⟨f, hfI, hf0, hexp⟩ | hdeg)
    · exact ⟨f, Ideal.mem_sup_left hfI, hf0, hexp⟩
    · have hmem : MvPowerSeries.monomial α (1 : R) ∈
          Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ n := by
        rw [MvPowerSeries.mem_span_range_X_pow_iff_forall_degree_lt]
        intro β hβ
        exact MvPowerSeries.coeff_monomial_ne (fun h : β = α ↦ hβ.not_ge (h ▸ hdeg)) (1 : R)
      refine ⟨MvPowerSeries.monomial α 1, Ideal.mem_sup_right hmem, ?_,
        degLex.initialExp_monomial_of_ne_zero α one_ne_zero⟩
      intro h0
      simpa using congrArg (MvPowerSeries.coeff (R := R) α) h0

/-- Over a field `K` and finite linearly ordered `σ`, the `degLex` initial diagram of
`I ⊔ 𝔪 ^ n` is `degLex.initialDiagram I ∪ {α | n ≤ α.degree}`. -/
theorem degLex_initialDiagram_sup_maximalIdeal_pow {σ K : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    degLex.initialDiagram (I ⊔ maximalIdeal (MvPowerSeries σ K) ^ n) =
      degLex.initialDiagram I ∪ {α : σ →₀ ℕ | n ≤ α.degree} := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
  exact degLex_initialDiagram_sup_span_range_X_pow I n

end DegLexTruncation

end MonomialOrder

namespace TauCeti

section DiagramCount

/-- **Hilbert–Samuel diagram counting**: over a field `K` and finite linearly ordered `σ`, the
Hilbert–Samuel value `localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ` equals the number of
exponents `α : σ →₀ ℕ` of total degree at most `ℓ` outside `degLex.initialDiagram I`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [Field K] [Finite σ] [LinearOrder σ]
    (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram I}.ncard : ℕ∞) := by
  have hcompl :
      (MonomialOrder.degLex.initialDiagram (I ⊔ maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)))ᶜ =
        {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram I} := by
    ext α
    simp [MonomialOrder.degLex_initialDiagram_sup_maximalIdeal_pow, and_comm]
  have hfin :
      (MonomialOrder.degLex.initialDiagram
        (I ⊔ maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)))ᶜ.Finite := by
    rw [hcompl]
    exact (Finsupp.finite_of_degree_le ℓ).subset fun _ h ↦ h.1
  rw [localQuotientHilbertSamuel_def,
    MonomialOrder.degLex.length_quotient_eq_ncard_compl_initialDiagram hfin, hcompl]

/-- Natural-number form of `localQuotientHilbertSamuel_mvPowerSeries`. -/
theorem toNat_localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    (localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ).toNat =
      {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram I}.ncard := by
  rw [localQuotientHilbertSamuel_mvPowerSeries, ENat.toNat_natCast]

/-- For `I = ⊥` on `MvPowerSeries σ K` (`σ` finite), `localQuotientHilbertSamuel` at `ℓ` is the
stars-and-bars binomial `(ℓ + Nat.card σ).choose (Nat.card σ)`. -/
@[simp]
theorem localQuotientHilbertSamuel_mvPowerSeries_bot {σ K : Type*} [Field K] [Finite σ] (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) ⊥ ℓ =
      ((ℓ + Nat.card σ).choose (Nat.card σ) : ℕ∞) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have hcard : Nat.card σ = n := by
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hbot : (⊥ : Ideal (MvPowerSeries σ K)).map (MvPowerSeries.renameEquiv K e).toRingEquiv =
      ⊥ := Ideal.map_bot
  rw [← localQuotientHilbertSamuel_map_equiv (MvPowerSeries.renameEquiv K e).toRingEquiv ⊥ ℓ,
    hbot, localQuotientHilbertSamuel_mvPowerSeries, MonomialOrder.initialDiagram_bot]
  simp [hcard, Finsupp.ncard_setOf_degree_le]

end DiagramCount

section Stabilization

/-- Over a field `K` and finite variable set `σ`, the set of lexicographically ordered
Hilbert–Samuel functions `{toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) I) | I}` is
well-founded in `Lex (ℕ → ℕ∞)`. -/
theorem isWF_toLex_localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [Field K] [Finite σ] :
    Set.IsWF (Set.range fun I : Ideal (MvPowerSeries σ K) ↦
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) I)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have hsub :
      (Set.range fun I : Ideal (MvPowerSeries σ K) ↦
        toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) I)) ⊆
      (Set.range fun J : Ideal (MvPowerSeries (Fin n) K) ↦
        toLex (localQuotientHilbertSamuel (MvPowerSeries (Fin n) K) J)) := by
    rintro _ ⟨I, rfl⟩
    refine ⟨I.map (MvPowerSeries.renameEquiv K e).toRingEquiv, ?_⟩
    funext ℓ
    exact localQuotientHilbertSamuel_map_equiv (MvPowerSeries.renameEquiv K e).toRingEquiv I ℓ
  refine Set.IsWF.mono ?_ hsub
  rw [Set.IsWF, Set.wellFoundedOn_iff_no_descending_seq]
  intro f hmem
  choose J hJ using hmem
  let c (k ℓ : ℕ) : ℕ :=
    {α : Fin n →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram (J k)}.ncard
  let g (k : ℕ) : Lex (ℕ → ℕ) := toLex (c k)
  have hg_mem (k : ℕ) : g k ∈
      {h : Lex (ℕ → ℕ) | ∃ D : Set (Fin n →₀ ℕ), IsUpperSet D ∧
        ofLex h = fun ℓ ↦ {α : Fin n →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D}.ncard} :=
    ⟨MonomialOrder.degLex.initialDiagram (J k),
      MonomialOrder.degLex.isUpperSet_initialDiagram (J k), rfl⟩
  have hc_cast (k ℓ : ℕ) : (c k ℓ : ℕ∞) = ofLex (f k) ℓ := by
    rw [← hJ k, ofLex_toLex, localQuotientHilbertSamuel_mvPowerSeries]
  have hg_anti : StrictAnti g := by
    refine strictAnti_nat_of_succ_lt fun k ↦ ?_
    have hfk : f (k + 1) < f k := f.map_rel_iff.mpr (Nat.lt_succ_self k)
    obtain ⟨ℓ₀, hpre, hlt⟩ := hfk
    dsimp only [g]
    refine ⟨ℓ₀, fun ℓ hℓ ↦ ?_, ?_⟩
    · exact Nat.cast_injective ((hc_cast (k + 1) ℓ).trans ((hpre ℓ hℓ).trans (hc_cast k ℓ).symm))
    · exact Nat.cast_lt.mp ((hc_cast (k + 1) ℓ₀).trans_lt (hlt.trans_eq (hc_cast k ℓ₀).symm))
  exact (Set.wellFoundedOn_iff_no_descending_seq.mp
    (Finsupp.isWF_toLex_ncard_setOf_degree_le_notMem (σ := Fin n)))
    ⟨⟨g, hg_anti.injective⟩, hg_anti.lt_iff_gt⟩ hg_mem

/-- Any sequence of ideals `I : ℕ → Ideal (MvPowerSeries σ K)` (`σ` finite) whose Hilbert–Samuel
functions are nonincreasing in `Lex (ℕ → ℕ∞)` stabilizes. -/
theorem exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex
    {σ K : Type*} [Field K] [Finite σ] (I : ℕ → Ideal (MvPowerSeries σ K))
    (hlex : ∀ j,
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1))) ≤
        toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) := by
  let S := Set.range fun J : Ideal (MvPowerSeries σ K) ↦
    toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) J)
  have : WellFoundedLT S := isWF_toLex_localQuotientHilbertSamuel_mvPowerSeries
  let seq (j : ℕ) : S := ⟨toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)), I j, rfl⟩
  have hanti : Antitone seq := antitone_nat_of_succ_le hlex
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition hanti
  exact ⟨j₀, fun j hj ↦ ofLex_inj.mpr (congrArg Subtype.val (hj₀ j hj)).symm⟩

/-- **Lexicographic stabilization of the Hilbert–Samuel function**: any sequence of ideals in
`MvPowerSeries (Fin n) K` whose Hilbert–Samuel functions are lexicographically nonincreasing
eventually stabilizes. -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  refine exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex I fun j ↦ ?_
  rcases h j with heq | hlt
  · exact le_of_eq (congrArg toLex heq)
  · exact le_of_lt hlt

/-- **Pointwise stabilization of the Hilbert–Samuel function**: any sequence of ideals in
`MvPowerSeries σ K` (`σ` finite) whose Hilbert–Samuel functions are pointwise nonincreasing at
every cutoff `ℓ` eventually stabilizes. -/
theorem exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone
    {σ K : Type*} [Field K] [Finite σ] (I : ℕ → Ideal (MvPowerSeries σ K))
    (hanti : ∀ j ℓ,
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) ℓ ≤
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) :=
  exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex I fun j ↦
    Pi.toLex_monotone (hanti j)

end Stabilization

end TauCeti

section Examples

open TauCeti MonomialOrder

/-- On `MvPowerSeries (Fin n) K`, the Hilbert–Samuel function of `⊥` at `ℓ` is `(n + ℓ).choose n`.
-/
example (K : Type*) [Field K] (n ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries (Fin n) K) ⊥ ℓ = ((n + ℓ).choose n : ℕ∞) := by
  rw [localQuotientHilbertSamuel_mvPowerSeries_bot, Nat.card_eq_fintype_card, Fintype.card_fin,
    add_comm]

/-- In `K⟦x⟧ = MvPowerSeries Unit K`, the ideal `(x²)` has Hilbert–Samuel values `1` at `ℓ = 0` and
`2` for all `1 ≤ ℓ`. -/
example (K : Type*) [Field K] :
    localQuotientHilbertSamuel (MvPowerSeries Unit K)
        (Ideal.span {MvPowerSeries.X () ^ 2}) 0 = 1 ∧
      ∀ ℓ, 1 ≤ ℓ →
        localQuotientHilbertSamuel (MvPowerSeries Unit K)
          (Ideal.span {MvPowerSeries.X () ^ 2}) ℓ = 2 := by
  refine ⟨?_, fun ℓ hℓ ↦ ?_⟩
  · refine localQuotientHilbertSamuel_zero_of_ne_top fun htop ↦ ?_
    have h1 : (1 : MvPowerSeries Unit K) ∈ Ideal.span {MvPowerSeries.X () ^ 2} :=
      htop ▸ Submodule.mem_top
    have hmem : (0 : Unit →₀ ℕ) ∈ degLex.initialDiagram
        (Ideal.span {MvPowerSeries.X () ^ 2} : Ideal (MvPowerSeries Unit K)) :=
      degLex.mem_initialDiagram_iff.mpr ⟨1, h1, one_ne_zero, by simp⟩
    rw [degLex.initialDiagram_span_X_pow, Set.mem_Ici] at hmem
    have h02 := hmem ()
    simp at h02
  · rw [localQuotientHilbertSamuel_mvPowerSeries, degLex.initialDiagram_span_X_pow]
    have hset : {α : Unit →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ Set.Ici (Finsupp.single () 2)} =
        ({0, Finsupp.single () 1} : Set (Unit →₀ ℕ)) := by
      ext α
      have hα : α = Finsupp.single () (α ()) := Finsupp.unique_single α
      conv_lhs => rw [hα]
      simp only [Set.mem_ofPred_eq, Set.mem_Ici, Finsupp.degree_single, Set.mem_insert_iff,
        Set.mem_singleton_iff, Finsupp.single_le_iff, Finsupp.single_eq_same]
      constructor
      · rintro ⟨_, hnot⟩
        have hlt : α () < 2 := lt_of_not_ge hnot
        interval_cases α ()
        · left
          rw [hα]
          simp
        · right
          rw [hα]
      · rintro (rfl | rfl) <;> simp; omega
    have hne : (0 : Unit →₀ ℕ) ≠ Finsupp.single () 1 := by
      intro h
      simpa using DFunLike.congr_fun h ()
    rw [hset, Set.ncard_pair hne]
    rfl

/-- For a degree-two field extension `L / k` (such as `ℂ / ℝ`), `L⟦x⟧` has
`localQuotientHilbertSamuel L⟦x⟧ ⊥ 0 = 1`, whereas `dim_k (L⟦x⟧ ⧸ 𝔪) = 2`. -/
example (k L : Type*) [Field k] [Field L] [Algebra k L] (hdeg : Module.finrank k L = 2) :
    localQuotientHilbertSamuel (MvPowerSeries Unit L) ⊥ 0 = 1 ∧
      Module.finrank k (MvPowerSeries Unit L ⧸ maximalIdeal (MvPowerSeries Unit L)) = 2 := by
  refine ⟨localQuotientHilbertSamuel_bot_zero, ?_⟩
  have hquot : (⊥ : Ideal (MvPowerSeries Unit L)) ⊔ maximalIdeal (MvPowerSeries Unit L) ^ (0 + 1) =
      maximalIdeal (MvPowerSeries Unit L) := by
    rw [bot_sup_eq, zero_add, pow_one]
  have hresL : IsLocalRing.ResidueField L ≃ₐ[k] L :=
    { __ := IsLocalRing.ResidueField.lift (RingHom.id L)
      invFun := IsLocalRing.residue L
      left_inv x := by
        obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
        rfl
      right_inv c := rfl
      commutes' c := rfl }
  have hfinrank : Module.finrank k (IsLocalRing.ResidueField (MvPowerSeries Unit L)) = 2 := by
    rw [LinearEquiv.finrank_eq
      ((MvPowerSeries.residueFieldAlgEquiv k (σ := Unit) (R := L)).trans hresL).toLinearEquiv,
      hdeg]
  rw [← hquot, finrank_quotient_sup_maximalIdeal_pow k ⊥ 0, localQuotientHilbertSamuel_bot_zero,
    ENat.toNat_one, one_mul, hfinrank]

/-- Decreasing powers `I j = (x ^ max (N - j) 1)` in `K⟦x⟧`: strictly decreasing in `Lex (ℕ → ℕ∞)`
for `j + 1 < N` and constant from `N - 1` onward. -/
example (K : Type*) [Field K] (N : ℕ) :
    let I : ℕ → Ideal (MvPowerSeries Unit K) :=
      fun j ↦ Ideal.span {MvPowerSeries.X () ^ max (N - j) 1}
    (∀ j, j + 1 < N →
      toLex (localQuotientHilbertSamuel (MvPowerSeries Unit K) (I (j + 1))) <
        toLex (localQuotientHilbertSamuel (MvPowerSeries Unit K) (I j))) ∧
    (∀ j, N - 1 ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries Unit K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries Unit K) (I (N - 1))) := by
  intro I
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_⟩
  · have hm₁ : max (N - (j + 1)) 1 = N - j - 1 := by omega
    have hm₀ : max (N - j) 1 = N - j := by omega
    refine ⟨N - j - 1, fun ℓ hℓ ↦ ?_, ?_⟩
    · dsimp only [I]
      rw [hm₁, hm₀]
      simp only [Pi.toLex_apply, localQuotientHilbertSamuel_mvPowerSeries,
        degLex.initialDiagram_span_X_pow]
      congr 2
      ext α
      have hα : α = Finsupp.single () (α ()) := Finsupp.unique_single α
      rw [hα]
      simp only [Set.mem_ofPred_eq, Set.mem_Ici, Finsupp.degree_single, Finsupp.single_le_iff,
        Finsupp.single_eq_same]
      omega
    · dsimp only [I]
      rw [hm₁, hm₀]
      simp only [Pi.toLex_apply, localQuotientHilbertSamuel_mvPowerSeries,
        degLex.initialDiagram_span_X_pow, Nat.cast_lt]
      refine Set.ncard_lt_ncard ?_ ((Finsupp.finite_of_degree_le _).subset fun _ h ↦ h.1)
      refine ⟨fun α ⟨hdeg, hnot⟩ ↦ ⟨hdeg, fun hge ↦ hnot ?_⟩, ?_⟩
      · rw [Set.mem_Ici, Finsupp.single_le_iff] at hge ⊢
        exact (Nat.sub_le _ _).trans hge
      · intro hsub
        let β : Unit →₀ ℕ := Finsupp.single () (N - j - 1)
        have hmem : β ∈
            {α : Unit →₀ ℕ | α.degree ≤ N - j - 1 ∧ α ∉ Set.Ici (Finsupp.single () (N - j))} := by
          refine ⟨?_, fun hge ↦ ?_⟩
          · simp only [β, Finsupp.degree_single]
            exact le_rfl
          · rw [Set.mem_Ici, Finsupp.single_le_iff] at hge
            simp only [β, Finsupp.single_eq_same] at hge
            omega
        exact (hsub hmem).2 (Set.mem_Ici.mpr le_rfl)
  · have hmax : max (N - j) 1 = max (N - (N - 1)) 1 := by omega
    dsimp only [I]
    rw [hmax]

end Examples
