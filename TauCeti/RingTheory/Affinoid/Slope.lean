/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Numerical slopes and slope decompositions

Let `K` be a nonarchimedean field and `A` a `K`-algebra. A polynomial `Q : A[X]` has *slope at
most `r`*, for a real cutoff `r > 0`, if for every `K`-algebra map `χ : A → L` into an algebraic
extension `L` of `K`, every root of `χ(Q)` has absolute value at least `r`. The absolute value of
a root is its spectral norm over `K`, which is the unique extension of the norm of `K` when `K` is
complete; no embedding into a chosen algebraic closure is involved. For `r = |p| ^ h` this says
that every root has valuation at most `h`. The condition concerns roots of an annihilating
polynomial, not of a Fredholm series `det (1 - T U)`, whose roots are the reciprocals.

For an affinoid algebra `A` the condition can be tested at the classical points: for each maximal
ideal `x` of `A`, whose residue field is finite over `K`, at the roots of `Q mod x` in a splitting
field of `Q mod x` over `A ⧸ x`, which is again finite over `K`. In particular it suffices to test
finite extensions of `K`. A root at an arbitrary algebraic point is conjugate over `K` to one of
these roots, and conjugate elements have the same spectral norm.

A *slope decomposition* of a continuous `A`-linear operator `U` on a topological `A`-module `M` is
a pair of topological complements `M₁, M₂` stable under `U`, such that `M₁` is finite projective
and is annihilated by `Q(U)` for a monic `Q` of slope at most `r` with unit constant term, while
every such polynomial acts bijectively on `M₂`. The continuous projection onto `M₁` along `M₂`
then commutes with `U`. Polynomial annihilation cannot be replaced by a pointwise condition on
eigenvalues: over a nonreduced base, or on a nilpotent operator, only the polynomial detects the
action.

## Main definitions

* `Polynomial.IsSlopeLE K r Q`: every root of `Q` at every algebraic point has absolute value at
  least `r > 0`.
* `ContinuousLinearMap.IsSlopeDecomposition K U r M₁ M₂`: `M = M₁ ⊕ M₂` is a slope `≤ r`
  decomposition for `U`.

## Main results

* `TauCeti.IsAffinoidAlgebra.isSlopeLE_iff_splittingField`: over an affinoid algebra the slope
  condition is tested at the roots of `Q mod x` in a splitting field, for maximal ideals `x`.
* `TauCeti.IsAffinoidAlgebra.isSlopeLE_iff_finiteDimensional`: over an affinoid algebra the slope
  condition is tested in finite extensions of `K`.
* `TauCeti.IsAffinoidAlgebra.le_spectralNorm_of_isSlopeLE`: over an affinoid algebra the slope
  condition applies to algebraic extensions of `K` in every universe.
* `ContinuousLinearMap.IsSlopeDecomposition.exists_projection`: a slope decomposition has a
  continuous idempotent projector with image `M₁` and kernel `M₂`, commuting with `U`.

## References

* E. Urban, *Eigenvarieties for reductive groups*, Ann. of Math. 174 (2011), 1685–1784, §2.3.
-/

public section

open Polynomial

universe v

namespace Polynomial

section IsSlopeLE

variable (K : Type*) [NormedField K] {A : Type v} [CommRing A] [Algebra K A]

/-- A polynomial `Q : A[X]` has slope at most `r` over `K` if `r > 0` and, for every `K`-algebra
map `χ : A → L` into an algebraic extension `L` of `K`, every root of `χ(Q)` has spectral norm at
least `r`. For `r = |p| ^ h` this says that every root has valuation at most `h`. -/
def IsSlopeLE (r : ℝ) (Q : A[X]) : Prop :=
  0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) (α : L),
    (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α

variable {K} {r s : ℝ} {P Q : A[X]}

/-- The defining property of `Polynomial.IsSlopeLE`. -/
theorem isSlopeLE_iff : Q.IsSlopeLE K r ↔
    0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L)
      (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α :=
  Iff.rfl

/-- The cutoff of the slope condition is positive. -/
theorem IsSlopeLE.pos (hQ : Q.IsSlopeLE K r) : 0 < r :=
  hQ.1

/-- Under the slope condition, every root of `χ(Q)` in an algebraic extension has spectral norm
at least the cutoff. -/
theorem IsSlopeLE.le_spectralNorm (hQ : Q.IsSlopeLE K r) {L : Type v} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L} (hα : (Q.map (χ : A →+* L)).IsRoot α) :
    r ≤ spectralNorm K L α :=
  hQ.2 L χ α hα

/-- Lowering a positive cutoff preserves the slope condition. -/
theorem IsSlopeLE.mono (hQ : Q.IsSlopeLE K r) (hs : 0 < s) (hsr : s ≤ r) : Q.IsSlopeLE K s :=
  ⟨hs, fun _ _ _ _ χ _ hα ↦ hsr.trans (hQ.le_spectralNorm χ hα)⟩

/-- The constant polynomial `1` has no roots, so it has slope at most every positive cutoff. -/
@[simp]
theorem isSlopeLE_one_iff : (1 : A[X]).IsSlopeLE K r ↔ 0 < r := by
  simp [isSlopeLE_iff]

/-- The roots of a product are the roots of its factors. -/
@[simp]
theorem isSlopeLE_mul_iff : (P * Q).IsSlopeLE K r ↔ P.IsSlopeLE K r ∧ Q.IsSlopeLE K r := by
  simp only [isSlopeLE_iff, Polynomial.map_mul, IsRoot, eval_mul, mul_eq_zero]
  exact ⟨fun h ↦ ⟨⟨h.1, fun L _ _ _ χ α hα ↦ h.2 L χ α (.inl hα)⟩,
    ⟨h.1, fun L _ _ _ χ α hα ↦ h.2 L χ α (.inr hα)⟩⟩,
    fun h ↦ ⟨h.1.1, fun L _ _ _ χ α hα ↦ hα.elim (h.1.2 L χ α) (h.2.2 L χ α)⟩⟩

/-- The linear polynomial `X - c` has slope at most `r` when `0 < r ≤ |c|`. -/
theorem isSlopeLE_X_sub_C_algebraMap {c : K} (hr : 0 < r) (hrc : r ≤ ‖c‖) :
    (X - C (algebraMap K A c)).IsSlopeLE K r := by
  refine ⟨hr, fun L _ _ _ χ α hα ↦ ?_⟩
  rw [Polynomial.map_sub, map_X, map_C, AlgHom.coe_toRingHom, AlgHom.commutes, IsRoot,
    eval_sub, eval_X, eval_C, sub_eq_zero] at hα
  rwa [hα, spectralNorm_extends]

/-- The polynomial `1 - c X`, whose root `c⁻¹` is the reciprocal of that of `X - c`, has slope
at most `r` when `0 < r ≤ |c|⁻¹`. -/
theorem isSlopeLE_one_sub_C_mul_X_algebraMap {c : K} (hr : 0 < r)
    (hrc : r ≤ ‖c‖⁻¹) : (1 - C (algebraMap K A c) * X).IsSlopeLE K r := by
  refine ⟨hr, fun L _ _ _ χ α hα ↦ ?_⟩
  rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_X, map_C,
    AlgHom.coe_toRingHom, AlgHom.commutes, IsRoot, eval_sub, eval_one, eval_mul, eval_X, eval_C,
    sub_eq_zero, eq_comm] at hα
  rwa [eq_inv_of_mul_eq_one_right hα, ← map_inv₀, spectralNorm_extends, norm_inv]

end IsSlopeLE

end Polynomial

namespace TauCeti.IsAffinoidAlgebra

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] {A : Type v} [CommRing A] [Algebra K A]
  {r : ℝ} {Q : A[X]}

/-- If, at every maximal ideal `x`, the reduction `Q mod x` is nonzero and its roots in a
splitting field over `A ⧸ x` have spectral norm at least `r`, then so does every root `α` of
`χ(Q)` in an algebraic extension `L` of `K`, in any universe. Indeed `α` lies over the maximal
ideal `ker χ`, and its minimal polynomial over `A ⧸ ker χ` has a root `β` in the splitting field;
`α` and `β` are then conjugate over `K`. -/
private theorem le_spectralNorm_of_forall_splittingField
    (h : ∀ x : MaximalSpectrum A,
      letI := Ideal.Quotient.field x.asIdeal
      Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
        ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
          (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
          r ≤ spectralNorm K _ β)
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L}
    (hα : (Q.map (χ : A →+* L)).IsRoot α) : r ≤ spectralNorm K L α := by
  -- `L` is integral over `A` along `χ`, so the kernel of `χ` is maximal.
  let : Algebra A L := (χ : A →+* L).toAlgebra
  have : IsScalarTower K A L := .of_algebraMap_eq fun c ↦ (χ.commutes c).symm
  have : Algebra.IsIntegral A L := .tower_top K
  set I := RingHom.ker χ
  have hI : I.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (χ : A →+* L)
    (fun y ↦ Algebra.IsIntegral.isIntegral (R := A) y) ⊥
  let := Ideal.Quotient.field I
  let F := A ⧸ I
  let Q' : F[X] := Q.map (Ideal.Quotient.mk I)
  obtain ⟨hQ', hroots⟩ := h ⟨I, hI⟩
  -- Make `L` an algebra over the residue field `F` through the injection `F → L` induced by `χ`.
  let : Algebra F L := (Ideal.kerLiftAlg χ : F →+* L).toAlgebra
  have : IsScalarTower K F L :=
    .of_algebraMap_eq fun c ↦ ((Ideal.kerLiftAlg χ).commutes c).symm
  have hmk : (algebraMap F L).comp (Ideal.Quotient.mk I) = (χ : A →+* L) :=
    RingHom.ext (Ideal.kerLiftAlg_mk χ)
  have hint : IsIntegral F α := (Algebra.IsIntegral.isIntegral (R := K) α).tower_top
  have hQα : aeval α Q' = 0 := by
    rwa [aeval_def, eval₂_map, hmk, ← eval_map]
  -- The minimal polynomial of `α` over `F` divides `Q mod x`, so it has a root in the splitting
  -- field of `Q mod x`.
  let S := Q'.SplittingField
  let q := minpoly F α
  have hdvd : q ∣ Q' := minpoly.dvd F α hQα
  obtain ⟨β, hβ⟩ := (SplittingField.splits Q').of_dvd (Polynomial.map_ne_zero hQ')
    (Polynomial.map_dvd _ hdvd) |>.exists_eval_eq_zero
      (by rw [degree_map]; exact (minpoly.degree_pos hint).ne')
  rw [eval_map_algebraMap] at hβ
  have hβQ : β ∈ Q'.rootSet S :=
    (mem_rootSet' (S := S)).2
      ⟨Polynomial.map_ne_zero hQ', aeval_eq_zero_of_dvd_aeval_eq_zero hdvd hβ⟩
  -- `α` and `β` are both images of the root of `q` under `K`-algebra maps of fields.
  have : Fact (Irreducible q) := ⟨minpoly.irreducible hint⟩
  let ψL : AdjoinRoot q →ₐ[K] L :=
    AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K F L) α (minpoly.aeval F α)
  let ψS : AdjoinRoot q →ₐ[K] S := AdjoinRoot.liftAlgHom q (IsScalarTower.toAlgHom K F S) β hβ
  calc r ≤ spectralNorm K S β := hroots β hβQ
    _ = spectralNorm K S (ψS (AdjoinRoot.root q)) :=
      congrArg _ (AdjoinRoot.liftAlgHom_root q _ β hβ).symm
    _ = spectralNorm K L (ψL (AdjoinRoot.root q)) := by
      rw [ψS.spectralNorm_map, ψL.spectralNorm_map]
    _ = spectralNorm K L α := congrArg _ (AdjoinRoot.liftAlgHom_root q _ α _)

variable [IsUltrametricDist K] [CompleteSpace K]

/-- If `Q` passes the slope test in finite extensions of `K`, then at every maximal ideal `x`, the
reduction `Q mod x` is nonzero and its roots in a splitting field have spectral norm at least
`r`. Both the residue field and the splitting field are finite over `K`. -/
private theorem forall_splittingField_of_finiteDimensional (hA : IsAffinoidAlgebra K A)
    (h : ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] (χ : A →ₐ[K] L)
      (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α) (hr : 0 < r)
    (x : MaximalSpectrum A) :
    letI := Ideal.Quotient.field x.asIdeal
    Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
      ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
        (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
        r ≤ spectralNorm K _ β := by
  let := Ideal.Quotient.field x.asIdeal
  have := hA.finite_quotient_of_isMaximal x.asIdeal
  refine ⟨fun h0 ↦ ?_, fun β hβ ↦ ?_⟩
  · -- If `Q mod x` vanished, then `0` would be a root of `Q` at the residue field of `x`.
    have := h (A ⧸ x.asIdeal) (Ideal.Quotient.mkₐ K x.asIdeal) 0
      (by simpa [IsRoot] using congrArg (eval 0) h0)
    rw [spectralNorm_zero] at this
    exact hr.not_ge this
  · let F := A ⧸ x.asIdeal
    let S := (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField
    have : FiniteDimensional K S := Module.Finite.trans F S
    refine h S ((IsScalarTower.toAlgHom K F S).comp (Ideal.Quotient.mkₐ K x.asIdeal)) β ?_
    rw [mem_rootSet] at hβ
    rw [IsRoot, ← hβ.2, aeval_def, eval₂_map, ← eval_map, AlgHom.comp_toRingHom]
    -- The ring maps underlying `IsScalarTower.toAlgHom` and `Ideal.Quotient.mkₐ` are
    -- `algebraMap` and `Ideal.Quotient.mk` by definition.
    rfl

/-- **Slope test at residue fields.** Over an affinoid algebra, `Q` has slope at most `r` if and
only if `r > 0` and, at every maximal ideal `x`, the reduction `Q mod x` is nonzero and each of
its roots in a splitting field over the finite residue field `A ⧸ x` has spectral norm at least
`r`. -/
theorem isSlopeLE_iff_splittingField (hA : IsAffinoidAlgebra K A) :
    Q.IsSlopeLE K r ↔ 0 < r ∧ ∀ x : MaximalSpectrum A,
      letI := Ideal.Quotient.field x.asIdeal
      Q.map (Ideal.Quotient.mk x.asIdeal) ≠ 0 ∧
        ∀ β ∈ (Q.map (Ideal.Quotient.mk x.asIdeal)).rootSet
          (Q.map (Ideal.Quotient.mk x.asIdeal)).SplittingField,
          r ≤ spectralNorm K _ β :=
  ⟨fun hQ ↦ ⟨hQ.pos, hA.forall_splittingField_of_finiteDimensional
    (fun _ _ _ _ χ _ hα ↦ hQ.le_spectralNorm χ hα) hQ.pos⟩,
    fun h ↦ ⟨h.1, fun _ _ _ _ χ _ hα ↦ le_spectralNorm_of_forall_splittingField h.2 χ hα⟩⟩

/-- **Slope test in finite extensions.** Over an affinoid algebra, `Q` has slope at most `r` if
and only if `r > 0` and every root of `χ(Q)` has spectral norm at least `r`, for every `K`-algebra
map `χ` from `A` to a finite extension of `K`. -/
theorem isSlopeLE_iff_finiteDimensional (hA : IsAffinoidAlgebra K A) :
    Q.IsSlopeLE K r ↔ 0 < r ∧ ∀ (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L]
      (χ : A →ₐ[K] L) (α : L), (Q.map (χ : A →+* L)).IsRoot α → r ≤ spectralNorm K L α :=
  ⟨fun hQ ↦ ⟨hQ.pos, fun _ _ _ _ χ _ hα ↦ hQ.le_spectralNorm χ hα⟩,
    fun h ↦ ⟨h.1, fun _ _ _ _ χ _ hα ↦ le_spectralNorm_of_forall_splittingField
      (hA.forall_splittingField_of_finiteDimensional h.2 h.1) χ hα⟩⟩

/-- Over an affinoid algebra, the slope condition bounds the roots of `χ(Q)` below by `r` for
algebraic extensions `L` of `K` in every universe, not only in the universe of `A` used in the
definition of `Polynomial.IsSlopeLE`. -/
theorem le_spectralNorm_of_isSlopeLE (hA : IsAffinoidAlgebra K A) (hQ : Q.IsSlopeLE K r)
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] (χ : A →ₐ[K] L) {α : L}
    (hα : (Q.map (χ : A →+* L)).IsRoot α) : r ≤ spectralNorm K L α :=
  le_spectralNorm_of_forall_splittingField ((hA.isSlopeLE_iff_splittingField).1 hQ).2 χ hα

end NontriviallyNormedField

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] {r : ℝ}

/-- Over a nonzero affinoid algebra, `X - c` has slope at most `r` exactly when `0 < r ≤ |c|`. In
particular `X - c` with `0 < |c| < 1` fails the test at `r = 1`. -/
theorem isSlopeLE_X_sub_C_algebraMap_iff [Nontrivial A] (hA : IsAffinoidAlgebra K A) {c : K} :
    (X - C (algebraMap K A c)).IsSlopeLE K r ↔ 0 < r ∧ r ≤ ‖c‖ := by
  refine ⟨fun h ↦ ⟨h.pos, ?_⟩, fun h ↦ isSlopeLE_X_sub_C_algebraMap h.1 h.2⟩
  obtain ⟨x, hx⟩ := Ideal.exists_maximal A
  let := Ideal.Quotient.field x
  have := hA.finite_quotient_of_isMaximal x
  have := h.le_spectralNorm (L := A ⧸ x) (Ideal.Quotient.mkₐ K x)
    (α := algebraMap K (A ⧸ x) c) (by simp)
  rwa [spectralNorm_extends] at this

end NormedField

end TauCeti.IsAffinoidAlgebra

namespace ContinuousLinearMap

variable (K : Type*) [NormedField K] {A : Type v} [CommRing A] [Algebra K A]
  {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]

/-- A slope `≤ r` decomposition `M = M₁ ⊕ M₂` of a continuous operator `U`: the submodules are
topological complements stable under `U`, the first summand is finite projective and annihilated
by `Q(U)` for some monic `Q` of slope at most `r` with unit constant term, and every such
polynomial acts bijectively on the second summand. -/
structure IsSlopeDecomposition (U : M →L[A] M) (r : ℝ) (M₁ M₂ : Submodule A M) : Prop where
  /-- The summands are complements, with continuous projection onto `M₁` along `M₂`. -/
  isTopCompl : M₁.IsTopCompl M₂
  /-- The first summand is stable under `U`. -/
  mem_invtSubmodule_left : M₁ ∈ Module.End.invtSubmodule (U : M →ₗ[A] M)
  /-- The second summand is stable under `U`. -/
  mem_invtSubmodule_right : M₂ ∈ Module.End.invtSubmodule (U : M →ₗ[A] M)
  /-- The first summand is a finite `A`-module. -/
  finite : Module.Finite A M₁
  /-- The first summand is a projective `A`-module. -/
  projective : Module.Projective A M₁
  /-- A monic polynomial of slope at most `r`, with unit constant term, kills `M₁` at `U`. -/
  exists_annihilator : ∃ Q : A[X], Q.Monic ∧ IsUnit (Q.coeff 0) ∧ Q.IsSlopeLE K r ∧
    M₁ ≤ LinearMap.ker (aeval (U : M →ₗ[A] M) Q)
  /-- Every monic polynomial of slope at most `r` with unit constant term is bijective on `M₂`
  at `U`. -/
  bijOn : ∀ P : A[X], P.Monic → IsUnit (P.coeff 0) → P.IsSlopeLE K r →
    Set.BijOn (aeval (U : M →ₗ[A] M) P) M₂ M₂

variable {K} {U : M →L[A] M} {r : ℝ} {M₁ M₂ : Submodule A M}

namespace IsSlopeDecomposition

/-- The cutoff of a slope decomposition is positive. -/
theorem pos (h : U.IsSlopeDecomposition K r M₁ M₂) : 0 < r :=
  let ⟨_, _, _, hQ, _⟩ := h.exists_annihilator
  hQ.pos

/-- The continuous projection onto the first summand along the second commutes with `U`. -/
theorem commute_projectionL (h : U.IsSlopeDecomposition K r M₁ M₂) :
    Commute (M₁.projectionL M₂ h.isTopCompl) U := by
  rw [ContinuousLinearMap.IsIdempotentElem.commute_iff
    (Submodule.isIdempotentElem_projectionL h.isTopCompl), Submodule.range_projectionL,
    Submodule.ker_projectionL]
  exact ⟨h.mem_invtSubmodule_left, h.mem_invtSubmodule_right⟩

/-- **The slope projector.** A slope decomposition has a continuous idempotent projector with
image `M₁` and kernel `M₂` that commutes with `U`. -/
theorem exists_projection (h : U.IsSlopeDecomposition K r M₁ M₂) :
    ∃ P : M →L[A] M, IsIdempotentElem P ∧ P.range = M₁ ∧ P.ker = M₂ ∧ Commute P U :=
  ⟨_, Submodule.isIdempotentElem_projectionL h.isTopCompl,
    Submodule.range_projectionL h.isTopCompl, Submodule.ker_projectionL h.isTopCompl,
    h.commute_projectionL⟩

end IsSlopeDecomposition

variable (K M)

/-- The zero operator has the slope decomposition `0 ⊕ M` at every positive cutoff. -/
theorem isSlopeDecomposition_zero_bot_top (hr : 0 < r) :
    (0 : M →L[A] M).IsSlopeDecomposition K r ⊥ ⊤ where
  isTopCompl := Submodule.isTopCompl_bot_top
  mem_invtSubmodule_left := (Module.End.mem_invtSubmodule _).2 bot_le
  mem_invtSubmodule_right := (Module.End.mem_invtSubmodule _).2 le_top
  finite := inferInstance
  projective := .of_free
  exists_annihilator := ⟨1, monic_one, by simp, isSlopeLE_one_iff.2 hr, bot_le⟩
  bijOn P _ hP _ := by
    rw [Submodule.top_coe, Set.bijOn_univ, ← Module.End.isUnit_iff,
      ContinuousLinearMap.toLinearMap_zero, ← coeff_zero_eq_aeval_zero']
    exact hP.map _

/-- On a finite projective module, the scalar operator `c` with `0 < r ≤ |c|` has the slope
decomposition `M ⊕ 0`. -/
theorem isSlopeDecomposition_algebraMap_smul_id_top_bot [ContinuousConstSMul A M]
    [Module.Finite A M] [Module.Projective A M] {c : K} (hr : 0 < r) (hrc : r ≤ ‖c‖) :
    (algebraMap K A c • ContinuousLinearMap.id A M).IsSlopeDecomposition K r ⊤ ⊥ where
  isTopCompl := Submodule.isTopCompl_top_bot
  mem_invtSubmodule_left := (Module.End.mem_invtSubmodule _).2 le_top
  mem_invtSubmodule_right := (Module.End.mem_invtSubmodule _).2 bot_le
  finite := .equiv Submodule.topEquiv.symm
  projective := .of_equiv Submodule.topEquiv.symm
  exists_annihilator := by
    have hc : c ≠ 0 := norm_pos_iff.1 (hr.trans_le hrc)
    refine ⟨X - C (algebraMap K A c), monic_X_sub_C _, ?_, isSlopeLE_X_sub_C_algebraMap hr hrc,
      fun m _ ↦ ?_⟩
    · simpa using (isUnit_iff_ne_zero.2 hc).map (algebraMap K A)
    · simp [Algebra.algebraMap_eq_smul_one]
  bijOn P _ _ _ := by
    rw [Submodule.bot_coe, Set.bijOn_singleton, map_zero]

end ContinuousLinearMap
