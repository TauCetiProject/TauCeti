/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.ProjectiveCoordinates
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Betti Poincaré series and matrix of graded projective resolutions

Let `A` be a `ℤ`-graded `k`-algebra and `bP` a `ℤ[q,q⁻¹]`-basis of the graded projective
Grothendieck group `K₀^gr(proj A)`. A concrete graded projective resolution `r` of a graded
`A`-module `M` whose terms `r.X n` are finitely generated over `A` defines a formal power series
vector over `ℤ[q,q⁻¹]`,

`B_M(q, t)_i = ∑_{n ≥ 0} [r.finiteProjectiveTerm n]_{bP, i} tⁿ ∈ ℤ[q,q⁻¹]⟦t⟧`,

tracking the graded projective coordinates of each resolution term without alternating signs or
cohomological finiteness assumptions. For an indexed family of resolved modules `M_j` (typically
the degree-zero simple modules `S_j`), `TauCeti.bettiPoincareMatrix` collects these series as
columns of a matrix `B(q, t)` whose rows are indexed by the projective basis `bP` and whose
columns are indexed by the resolved modules, dual to the row/column convention of
`TauCeti.gradedCartanMatrix`.

Because minimal graded projective resolutions with bounded-below (and in particular finitely
generated, over a nonnegatively graded algebra) terms are unique up to chain isomorphism
(`TauCeti.GradedProjectiveResolution.IsMinimal.termObjIsoOfIso`), the Betti Poincaré series of a
minimal resolution depends only on the graded isomorphism class of `M`, not on the chosen minimal
resolution. Shifting `M` to `M{d}` shifts any minimal resolution termwise and multiplies its Betti
Poincaré series by `qᵈ` (`PowerSeries.C (LaurentPolynomial.T d)`).

## Main definitions

* `TauCeti.bettiPoincareSeries`: the `I`-indexed Betti Poincaré series in
  `PowerSeries (LaurentPolynomial ℤ)` of a finite-term `GradedProjectiveResolution` relative to a
  basis `bP` of `K₀^gr(proj A)`.
* `TauCeti.bettiPoincareMatrix`: the `I × J` matrix over `PowerSeries (LaurentPolynomial ℤ)` with
  `(i, j)` entry `bettiPoincareSeries bP (r j) i` (rows indexed by projectives, columns by
  resolved modules).
* `TauCeti.GradedProjectiveResolution.ofShortExact`: the two-term graded projective resolution
  `0 ⟶ P₁ ⟶ P₀ ⟶ M ⟶ 0` attached to a short exact sequence with projective `P₁` and `P₀`.

## Main results

* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_iso` and
  `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_of_iso_of_finite`:
  invariance of the Betti Poincaré series across bounded-below (or finite-term over a
  nonnegatively graded algebra) minimal resolutions of isomorphic graded modules.
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareMatrix_eq_of_finite`: independence of
  the Betti Poincaré matrix from the chosen finite-term minimal resolutions.
* `TauCeti.bettiPoincareSeries_shiftObj` and `TauCeti.bettiPoincareSeries_shiftObj_one`: shifting
  a resolution from `M` to `M{d}` multiplies its Betti Poincaré series by `C (T d)` (and by
  `C (T 1)` for `d = 1`).
* `TauCeti.GradedProjectiveResolution.IsMinimal.bettiPoincareSeries_eq_C_T_mul_of_shiftObj`:
  minimal-resolution shift law relating any minimal resolution of `M{d}` to any minimal resolution
  of `M`.
* `TauCeti.bettiPoincareSeries_eq_sum_of_forall_subsingleton` and
  `TauCeti.GradedProjectiveResolution.bettiPoincareSeries_ofShortExact`: finite and two-term
  projective resolutions have polynomial Betti Poincaré series (`[P₀] + [P₁] t` in the two-term
  case).

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *J. Amer. Math. Soc.* **9** (1996), Sections 1.2 and 2.11.
* Z. Dancso and A. Licata, "Koszul algebras and flow lattices", *J. Combin. Theory Ser. A*
  **185** (2022), Sections 2.2 and 3.1.
* D. Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Graduate Texts in
  Mathematics **150**, Springer (1995), Chapter 19, for minimal graded free/projective resolutions
  and graded Betti numbers.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI uJ

section Definitions

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}
  {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

/-- **The Betti Poincaré series** of a graded projective resolution `r` with finitely generated
terms, relative to a `ℤ[q,q⁻¹]`-basis `bP` of `K₀^gr(proj A)`. Its `n`th power-series coefficient
at `i` is the `i`th coordinate of `[r.finiteProjectiveTerm n]` in `bP`. -/
def bettiPoincareSeries {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) :
    PowerSeries (LaurentPolynomial ℤ) :=
  PowerSeries.mk fun n =>
    bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      (r.finiteProjectiveTerm n)) i

/-- The coefficient of `tⁿ` in `bettiPoincareSeries bP r i` is the `i`th coordinate of the `n`th
resolution term in the projective basis `bP`. -/
@[simp]
theorem coeff_bettiPoincareSeries {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (n : ℕ) :
    PowerSeries.coeff n (bettiPoincareSeries bP r i) =
      bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
        (r.finiteProjectiveTerm n)) i := by
  simp [bettiPoincareSeries]

/-- **The Betti Poincaré matrix** `B(q, t)` of an indexed family of finite-term graded projective
resolutions `r j` relative to a projective basis `bP`: rows are indexed by `I` (projectives) and
columns by `J` (resolved modules). -/
def bettiPoincareMatrix {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] :
    Matrix I J (PowerSeries (LaurentPolynomial ℤ)) :=
  Matrix.of fun i j => bettiPoincareSeries bP (r j) i

/-- Entry `(i, j)` of `bettiPoincareMatrix bP r` is the `i`th coordinate series of `r j`. -/
@[simp]
theorem bettiPoincareMatrix_apply {M : J → GradedModuleCat.{uA} 𝒜}
    (r : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading)
    [∀ j n, Module.Finite A ((r j).X n)] (i : I) (j : J) :
    bettiPoincareMatrix bP r i j = bettiPoincareSeries bP (r j) i :=
  (rfl)

/-- A subsingleton resolution term contributes zero to the Betti Poincaré series in that
homological degree. -/
theorem coeff_bettiPoincareSeries_of_subsingleton {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) {n : ℕ} (hn : Subsingleton (r.X n)) :
    PowerSeries.coeff n (bettiPoincareSeries bP r i) = 0 := by
  have hsub : Subsingleton (r.finiteProjectiveTerm n).obj.carrier := by
    rw [r.finiteProjectiveTerm_obj n]
    exact hn
  have hZ : Limits.IsZero (r.finiteProjectiveTerm n) :=
    (Limits.IsZero.iff_id_eq_zero _).mpr <| ObjectProperty.hom_ext _ <|
      GradedModuleCat.hom_ext <| LinearMap.ext fun _ => hsub.elim _ _
  rw [coeff_bettiPoincareSeries, ← LaurentK0.ofExactK0_exactK0_of.{uA},
    ExactK0.of_eq_zero_of_isZero.{uA} hZ, map_zero, map_zero, Finsupp.zero_apply]

/-- When all terms of `r` in homological degree `≥ N` are subsingletons, `bettiPoincareSeries` is
a finite polynomial in `PowerSeries.X`. -/
theorem bettiPoincareSeries_eq_sum_of_forall_subsingleton {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) (N : ℕ)
    (hN : ∀ n ≥ N, Subsingleton (r.X n)) :
    bettiPoincareSeries bP r i =
      ∑ m ∈ Finset.range N,
        PowerSeries.C (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (r.finiteProjectiveTerm m)) i) * PowerSeries.X ^ m := by
  ext n
  rw [map_sum]
  by_cases hn : n < N
  · rw [Finset.sum_eq_single n]
    · simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    · intro m _ hmn
      simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, Ne.symm hmn]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hn) hmem
  · rw [coeff_bettiPoincareSeries_of_subsingleton bP r i (hN n (Nat.le_of_not_lt hn)),
      Finset.sum_eq_zero]
    intro m hm
    have hmn : n ≠ m :=
      Nat.ne_of_gt (lt_of_lt_of_le (Finset.mem_range.mp hm) (Nat.le_of_not_lt hn))
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, hmn]

/-! ### Shift law -/

/-- **Shift law for the Betti Poincaré series**: shifting a graded projective resolution from `M`
to `M{d}` multiplies every entry of its Betti Poincaré series by `C (T d)` (`qᵈ`). -/
@[simp]
theorem bettiPoincareSeries_shiftObj {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (d : ℤ) (i : I) :
    bettiPoincareSeries bP (r.shiftObj d) i =
      PowerSeries.C (T d) * bettiPoincareSeries bP r i := by
  ext n
  rw [PowerSeries.coeff_C_mul, coeff_bettiPoincareSeries, coeff_bettiPoincareSeries]
  let Q : (gradedFiniteProjectiveModules 𝒜).FullSubcategory :=
    ⟨(r.finiteProjectiveTerm n).obj.shiftObj d,
      gradedFiniteProjectiveModules_shiftObj (r.finiteProjectiveTerm n).property d⟩
  have hiso : ((r.shiftObj d).finiteProjectiveTerm n).obj ≅ Q.obj :=
    eqToIso (by simp [Q])
  rw [LaurentK0.of_congr.{uA} _ (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (X := (r.shiftObj d).finiteProjectiveTerm n) (Y := Q) hiso),
    laurentK0_projective_of_shiftObj, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Shifting `M` by `1` multiplies every entry of its Betti Poincaré series by `C (T 1)` (`q`). -/
theorem bettiPoincareSeries_shiftObj_one {M : GradedModuleCat.{uA} 𝒜}
    (r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading)
    [∀ n, Module.Finite A (r.X n)] (i : I) :
    bettiPoincareSeries bP (r.shiftObj 1) i =
      PowerSeries.C (T 1) * bettiPoincareSeries bP r i :=
  bettiPoincareSeries_shiftObj bP r 1 i

end Definitions

/-! ### Uniqueness for minimal resolutions -/

namespace GradedProjectiveResolution

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
  {I : Type uI} {J : Type uJ}
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))

/-- **Isomorphic graded modules with bounded-below minimal resolutions have the same Betti
Poincaré series.** -/
theorem IsMinimal.bettiPoincareSeries_eq_of_iso {M M' : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M'.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (φ : M ≅ M') (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (hbelow : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hbelow' : ∀ n, ∃ b : ℤ, ∀ p < b, (r'.grading n).piece p = ⊥) (i : I) :
    bettiPoincareSeries bP r i = bettiPoincareSeries bP r' i := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_bettiPoincareSeries, coeff_bettiPoincareSeries]
  congr 2
  exact LaurentK0.of_congr.{uA} _
    (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (X := r.finiteProjectiveTerm n) (Y := r'.finiteProjectiveTerm n)
      (eqToIso (r.finiteProjectiveTerm_obj n) ≪≫
        hr.termObjIsoOfIso φ hr' hbelow hbelow' n ≪≫
        (eqToIso (r'.finiteProjectiveTerm_obj n)).symm))

/-- **Independence of the Betti Poincaré series from the chosen bounded-below minimal
resolution.** -/
theorem IsMinimal.bettiPoincareSeries_eq {M : GradedModuleCat.{uA} 𝒜}
    {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal)
    (hbelow : ∀ n, ∃ b : ℤ, ∀ p < b, (r.grading n).piece p = ⊥)
    (hbelow' : ∀ n, ∃ b : ℤ, ∀ p < b, (r'.grading n).piece p = ⊥) (i : I) :
    bettiPoincareSeries bP r i = bettiPoincareSeries bP r' i :=
  hr.bettiPoincareSeries_eq_of_iso bP (Iso.refl M) hr' hbelow hbelow' i

/-- **Over a nonnegatively graded algebra, the Betti Poincaré series of a finite-term minimal
resolution depends only on the graded isomorphism class of the resolved module.** -/
theorem IsMinimal.bettiPoincareSeries_eq_of_iso_of_finite (hneg : ∀ p < 0, 𝒜 p = ⊥)
    {M M' : GradedModuleCat.{uA} 𝒜}
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M'.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (φ : M ≅ M') (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    bettiPoincareSeries bP r i = bettiPoincareSeries bP r' i :=
  hr.bettiPoincareSeries_eq_of_iso bP φ hr'
    (fun n => (r.grading n).exists_piece_eq_bot_of_lt 𝒜 hneg)
    (fun n => (r'.grading n).exists_piece_eq_bot_of_lt 𝒜 hneg) i

/-- **Over a nonnegatively graded algebra, any two finite-term minimal resolutions of `M` define
the same Betti Poincaré series.** -/
theorem IsMinimal.bettiPoincareSeries_eq_of_finite (hneg : ∀ p < 0, 𝒜 p = ⊥)
    {M : GradedModuleCat.{uA} 𝒜}
    {r r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    bettiPoincareSeries bP r i = bettiPoincareSeries bP r' i :=
  hr.bettiPoincareSeries_eq_of_iso_of_finite bP hneg (Iso.refl M) hr' i

/-- **Over a nonnegatively graded algebra, the Betti Poincaré matrix of a family of modules is
independent of the chosen finite-term minimal resolutions.** -/
theorem IsMinimal.bettiPoincareMatrix_eq_of_finite (hneg : ∀ p < 0, 𝒜 p = ⊥)
    {M : J → GradedModuleCat.{uA} 𝒜}
    {r r' : ∀ j, GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M j).grading}
    [∀ j n, Module.Finite A ((r j).X n)] [∀ j n, Module.Finite A ((r' j).X n)]
    (hr : ∀ j, (r j).IsMinimal) (hr' : ∀ j, (r' j).IsMinimal) :
    bettiPoincareMatrix bP r = bettiPoincareMatrix bP r' := by
  refine Matrix.ext fun i j => ?_
  rw [bettiPoincareMatrix_apply, bettiPoincareMatrix_apply,
    (hr j).bettiPoincareSeries_eq_of_finite bP hneg (hr' j) i]

/-- **Minimal-resolution shift law**: over a nonnegatively graded algebra, for any finite-term
minimal resolutions `r` of `M` and `r'` of `M{d}`, the Betti Poincaré series of `r'` is `C (T d)`
times that of `r`. -/
theorem IsMinimal.bettiPoincareSeries_eq_C_T_mul_of_shiftObj (hneg : ∀ p < 0, 𝒜 p = ⊥)
    {M : GradedModuleCat.{uA} 𝒜} (d : ℤ)
    {r : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 M.grading}
    {r' : GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 (M.shiftObj d).grading}
    [∀ n, Module.Finite A (r.X n)] [∀ n, Module.Finite A (r'.X n)]
    (hr : r.IsMinimal) (hr' : r'.IsMinimal) (i : I) :
    bettiPoincareSeries bP r' i = PowerSeries.C (T d) * bettiPoincareSeries bP r i := by
  rw [hr'.bettiPoincareSeries_eq_of_finite bP hneg ((r.isMinimal_shiftObj_iff d).mpr hr) i,
    bettiPoincareSeries_shiftObj]

/-! ### Resolutions of length one from short exact sequences -/

/-- The `n`th graded module of a length-one projective resolution built from a short complex `S`:
`S.X₂` in degree `0`, `S.X₁` in degree `1`, and the empty direct sum in degrees `≥ 2`. -/
abbrev shortExactTerm (S : ShortComplex (GradedModuleCat.{uA} 𝒜)) :
    ℕ → GradedModuleCat.{uA} 𝒜
  | 0 => S.X₂
  | 1 => S.X₁
  | _ + 2 => GradedModuleCat.directSumObj (Empty.elim : Empty → GradedModuleCat.{uA} 𝒜)

/-- The `n`th differential of `ofShortExact`: `S.f.hom` at `n = 0` and `0` in degrees `≥ 1`. -/
abbrev shortExactDiff (S : ShortComplex (GradedModuleCat.{uA} 𝒜)) :
    ∀ n, (shortExactTerm S (n + 1)).carrier →ₗ[A] (shortExactTerm S n).carrier
  | 0 => S.f.hom
  | _ + 1 => 0

/-- **Length-one graded projective resolution from a short exact sequence**
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` whose left and middle terms are projective over `A`, padded by
empty direct sums in homological degrees `≥ 2`. -/
@[expose]
def ofShortExact {S : ShortComplex (GradedModuleCat.{uA} 𝒜)} (hS : S.ShortExact)
    [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    GradedProjectiveResolution.{uk, uA, uA, uA} 𝒜 S.X₃.grading where
  X n := (shortExactTerm S n).carrier
  addCommGroup n := (shortExactTerm S n).isAddCommGroup
  module n := (shortExactTerm S n).isModule
  moduleBase n := (shortExactTerm S n).isModuleBase
  isScalarTower n := (shortExactTerm S n).isScalarTower
  grading n := (shortExactTerm S n).grading
  gradedSMul n := (shortExactTerm S n).gradedSMul
  projective
    | 0 => inferInstanceAs (Module.Projective A S.X₂)
    | 1 => inferInstanceAs (Module.Projective A S.X₁)
    | _ + 2 =>
        let _ (e : Empty) : Module.Projective A (Empty.elim e : GradedModuleCat.{uA} 𝒜) := e.elim
        inferInstanceAs (Module.Projective A
          (DirectSum Empty fun e => (Empty.elim e : GradedModuleCat.{uA} 𝒜)))
  d := shortExactDiff S
  π := S.g.hom
  isHomogeneous_d
    | 0 => S.f.isHomogeneous
    | _ + 1 => LinearMap.isHomogeneous_def.2 fun _ _ _ => Submodule.zero_mem _
  isHomogeneous_π := S.g.isHomogeneous
  surjective_π := by
    have := hS.epi_g
    exact (GradedModuleCat.epi_iff_surjective S.g).mp inferInstance
  exact_d_π := GradedModuleCat.exact_iff.mp hS.exact
  exact_d_d
    | 0 => fun x => by
        have := hS.mono_f
        have hf : Function.Injective S.f.hom :=
          (GradedModuleCat.mono_iff_injective S.f).mp inferInstance
        exact ⟨fun hx => ⟨0, hf (hx.trans (map_zero S.f.hom).symm) ▸ rfl⟩,
          by rintro ⟨_, rfl⟩; exact map_zero S.f.hom⟩
    | _ + 1 => fun x =>
        ⟨fun _ => ⟨0, DFinsupp.ext fun e => e.elim⟩, fun _ => rfl⟩

omit [GradedAlgebra 𝒜] in
instance moduleFinite_ofShortExact {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) [Module.Projective A S.X₁] [Module.Projective A S.X₂]
    [Module.Finite A S.X₁] [Module.Finite A S.X₂] :
    ∀ n, Module.Finite A ((ofShortExact hS).X n)
  | 0 => inferInstanceAs (Module.Finite A S.X₂)
  | 1 => inferInstanceAs (Module.Finite A S.X₁)
  | _ + 2 =>
      ⟨⟨∅, Submodule.eq_top_iff'.mpr fun x =>
        (DFinsupp.ext fun e => e.elim : x = 0) ▸ Submodule.zero_mem _⟩⟩

omit [GradedAlgebra 𝒜] in
/-- `ofShortExact hS` is minimal if and only if `S.f` lands in `A₊ S.X₂`. -/
theorem isMinimal_ofShortExact_iff {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) [Module.Projective A S.X₁] [Module.Projective A S.X₂] :
    (ofShortExact hS).IsMinimal ↔
      ∀ x : S.X₁, S.f.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k S.X₂) := by
  rw [isMinimal_iff]
  refine ⟨fun h => h 0, fun h n => ?_⟩
  cases n with
  | zero => exact h
  | succ _ => exact fun _ => Submodule.zero_mem _

omit [GradedAlgebra 𝒜] in
/-- **Betti Poincaré series of a length-one projective resolution.** For a short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` of finite graded projectives, `bettiPoincareSeries` is linear in
`PowerSeries.X`, with constant term `[S.X₂]` and linear coefficient `[S.X₁]`. -/
theorem bettiPoincareSeries_ofShortExact {S : ShortComplex (GradedModuleCat.{uA} 𝒜)}
    (hS : S.ShortExact) [Module.Projective A S.X₁] [Module.Projective A S.X₂]
    [Module.Finite A S.X₁] [Module.Finite A S.X₂]
    (hP₁ : gradedFiniteProjectiveModules 𝒜 S.X₁)
    (hP₂ : gradedFiniteProjectiveModules 𝒜 S.X₂) (i : I) :
    bettiPoincareSeries bP (ofShortExact hS) i =
      PowerSeries.C (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨S.X₂, hP₂⟩) i) +
        PowerSeries.C (bP.repr (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          ⟨S.X₁, hP₁⟩) i) * PowerSeries.X := by
  have htail : ∀ n ≥ 2, Subsingleton ((ofShortExact hS).X n) := fun n hn => by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact ⟨fun _ _ => DFinsupp.ext fun e => e.elim⟩
  rw [bettiPoincareSeries_eq_sum_of_forall_subsingleton bP (ofShortExact hS) i 2 htail,
    Finset.sum_range_succ, Finset.sum_range_one, pow_zero, mul_one, pow_one]
  have h0 : LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      ((ofShortExact hS).finiteProjectiveTerm 0) =
      LaurentK0.of.{uA} _ ⟨S.X₂, hP₂⟩ :=
    LaurentK0.of_congr.{uA} _ (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (eqToIso (((ofShortExact hS).finiteProjectiveTerm_obj 0))))
  have h1 : LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
      ((ofShortExact hS).finiteProjectiveTerm 1) =
      LaurentK0.of.{uA} _ ⟨S.X₁, hP₁⟩ :=
    LaurentK0.of_congr.{uA} _ (ObjectProperty.isoMk (gradedFiniteProjectiveModules 𝒜)
      (eqToIso (((ofShortExact hS).finiteProjectiveTerm_obj 1))))
  rw [h0, h1]

end GradedProjectiveResolution

end TauCeti
