/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Hom
public import TauCeti.Algebra.Module.GradedModule.Internal

/-!
# Lifting maps out of row-finite semi-free modules along quasi-isomorphisms

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)` which is
one-sided, `m x y = 0` whenever `ind x ≤ ind y`, and whose generator indices are bounded below, as
for the cells of a CW complex. Its free differential graded left module `K_m = P →₀ A` is then
built from zero by attaching free generators along cycles, one index at a time, so it is a
**semi-free** module. This file proves that such modules are **K-projective** and **cofibrant**.

Let `φ : N → N'` be a degree-preserving `A`-linear map of differential graded left modules whose
relative cycles are relative boundaries: every `(c, w)` with `dN c = 0` and `φ c = dN' w` is
`(dN u, φ u + dN' v)`. This is the elementwise statement that the mapping cone of `φ` is acyclic,
that is, that `φ` is a quasi-isomorphism; for right modules it is
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`. Then every relative cycle of the map of
complexes of graded maps `Hom(K_m, N) → Hom(K_m, N')` is a relative boundary
(`TauCeti.RowFiniteTwistingCocycle.exists_rowFiniteHomDifferential_eq_of_forall_exists`). Graded
maps out of `K_m` are written by their generator values, with the differential
`TauCeti.rowFiniteHomDifferential` of `TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Hom`.

The proof builds the bounding maps one index level at a time. On a generator `x`, the
differential of graded maps only reads the generator values on the row of `x`, which lie in
strictly lower levels, so the obstruction at `x` is a relative cycle of `φ` itself; since `φ` is a
quasi-isomorphism it is a relative boundary, and its homogeneous components give the values at
`x`. Generators of one level do not interact, and the lower bound on the indices starts the
induction.

In degrees `0` and `1` this gives the lifting properties of maps of differential graded modules:

* `TauCeti.RowFiniteTwistingCocycle.exists_lift_homotopy`: every degree-preserving chain map
  `g : K_m → N'` lifts, up to homotopy, along `φ`. That is, there are a degree-preserving chain
  map `ĝ : K_m → N` and a homotopy `H` of degree `-1` with `g - φ ∘ ĝ = dN' ∘ H + H ∘ D`.
* `TauCeti.RowFiniteTwistingCocycle.exists_nullHomotopy_of_forall_exists`: a chain map `K_m → N`
  whose composite with `φ` is null-homotopic is itself null-homotopic.
* `TauCeti.RowFiniteTwistingCocycle.exists_nullHomotopy`: every chain map from `K_m` to an
  acyclic DG left module is null-homotopic.
* `TauCeti.RowFiniteTwistingCocycle.exists_lift`: every chain map `K_m → N'` lifts strictly along
  a surjective quasi-isomorphism `N → N'`.

A map out of the free module is given by the images of the generators, through
`Finsupp.linearCombination`, and a map of degree `-1` by the signed map
`TauCeti.rowFiniteSignedMap` of the images of the generators, which carries the Koszul sign of
the coefficient. Both laws are checked on generators
(`TauCeti.linearCombination_rowFiniteTwistedDifferential` and
`TauCeti.linearCombination_eq_add_rowFiniteSignedMap`).

Together the lifting and uniqueness properties show that a quasi-isomorphism between two such
semi-free modules, given by a continuation cocycle, has a homotopy inverse given by a continuation
cocycle, so the two twisting cocycles are homologous
(`TauCeti.RowFiniteContinuationCocycle.exists_rowFiniteHomologous_of_forall_exists`). By
`TauCeti.RowFiniteHomologous.homotopyEquiv`, the twisted complexes `M ⊗ ⟨P⟩` and `M ⊗ ⟨Q⟩` are
then homotopy equivalent for every differential graded right module `M`. With the invariance in
the coefficient module, `TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap`,
this says that the twisted complex computes a derived tensor product: it depends on the
semi-free module only up to quasi-isomorphism.

For free targets, the cycles of degree `0` of the complex of graded maps `K_mP → K_mQ` are the
continuation cocycles (`TauCeti.RowFiniteContinuationCocycle.ofRowFiniteHomDifferential`), and the
families of degree `-1` bounding `ν₁ - ν₀` are the parametrized cocycles
(`TauCeti.RowFiniteParametrizedCocycle.ofRowFiniteHomDifferential`). Precomposing a parametrized
cocycle with a continuation cocycle gives a parametrized cocycle
(`TauCeti.RowFiniteParametrizedCocycle.whiskerLeft`).

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, GTM 205, Springer, 2001,
  Chapter 6 (semifree modules and the lifting lemma).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open DirectSum

namespace TauCeti

universe uR uA uN uN' uP uQ uS

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}

/-! ### Precomposition with a continuation cocycle -/

section Continuation

variable {P : Type uP} {Q : Type uQ} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {dN : N →ₗ[R] N}

/-- **Precomposition with a continuation cocycle commutes with the differential of graded
maps**: for a continuation cocycle `ν` from `mP` to `mQ`, the differential of the generator
values `x ↦ Ψ_u (ν x)` of `Ψ_u ∘ ν` is `x ↦ Ψ_(δ u) (ν x)`. -/
theorem RowFiniteContinuationCocycle.rowFiniteHomDifferential_comp
    (ν : RowFiniteContinuationCocycle mP mQ) (hN : IsDGLeftModule hA 𝒩 dN) (j : ℤ) (u : Q → N) :
    rowFiniteHomDifferential 𝒜 mP.m dN j (fun x ↦ rowFiniteSignedMap 𝒜 j u (ν.ν x)) =
      fun x ↦ rowFiniteSignedMap 𝒜 (j + 1) (rowFiniteHomDifferential 𝒜 mQ.m dN j u)
        (ν.ν x) := by
  funext x
  rw [rowFiniteSignedMap_rowFiniteHomDifferential hN, ν.continuation,
    rowFiniteSignedMap_linearCombination, rowFiniteHomDifferential_apply]

end Continuation

/-! ### Cocycles between free modules as cycles of the complex of graded maps -/

section FreeTarget

variable {P : Type uP} {Q : Type uQ} {S : Type uS} {indP : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {mS : RowFiniteTwistingCocycle 𝒜 d S indS}

/-- The rows of a continuation cocycle are a cycle of degree `0` of the complex of graded maps
`K_mP → K_mQ`. -/
theorem RowFiniteContinuationCocycle.rowFiniteHomDifferential_ν
    (ν : RowFiniteContinuationCocycle mP mQ) :
    rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m) 0
      ν.ν = 0 :=
  (forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mp
    fun x ↦ (ν.continuation x).symm

/-- A cycle of degree `0` of the complex of graded maps `K_mP → K_mQ`, whose row at each `x` has
total degree `-indP x`, is a continuation cocycle. -/
def RowFiniteContinuationCocycle.ofRowFiniteHomDifferential (ν : P → Q →₀ A)
    (hν : ∀ x, ν x ∈ rowFiniteTotalGrading 𝒜 indQ (-indP x))
    (hδ : rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m)
      0 ν = 0) :
    RowFiniteContinuationCocycle mP mQ where
  ν := ν
  mem_graded x y := by
    simpa only [neg_add_eq_sub] using (mem_rowFiniteTotalGrading_iff _ _).mp (hν x) y
  continuation x :=
    ((forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mpr hδ x).symm

/-- The rows of a parametrized cocycle from `ν₀` to `ν₁` bound `ν₁ - ν₀` in the complex of graded
maps `K_mP → K_mQ`. -/
theorem RowFiniteParametrizedCocycle.rowFiniteHomDifferential_h
    {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ} (H : RowFiniteParametrizedCocycle ν₀ ν₁) :
    rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m) (-1)
      H.h = ν₁.ν - ν₀.ν :=
  funext fun x ↦ by rw [rowFiniteHomDifferential_neg_one_apply, H.parametrized, Pi.sub_apply]

/-- A family of degree `-1` of the complex of graded maps `K_mP → K_mQ`, whose row at each `x`
has total degree `-1 - indP x` and whose differential is `ν₁ - ν₀`, is a parametrized cocycle
from `ν₀` to `ν₁`. -/
def RowFiniteParametrizedCocycle.ofRowFiniteHomDifferential
    {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ} (h : P → Q →₀ A)
    (hh : ∀ x, h x ∈ rowFiniteTotalGrading 𝒜 indQ (-1 - indP x))
    (hδ : rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m)
      (-1) h = ν₁.ν - ν₀.ν) :
    RowFiniteParametrizedCocycle ν₀ ν₁ where
  h := h
  mem_graded x y := by
    convert (mem_rowFiniteTotalGrading_iff _ _).mp (hh x) y using 2
    ring
  parametrized x := by rw [← rowFiniteHomDifferential_neg_one_apply, hδ, Pi.sub_apply]

/-- **Precomposing a parametrized cocycle with a continuation cocycle.** For a continuation
cocycle `μ` from `mS` to `mP` and a parametrized cocycle `H` from `ν₀` to `ν₁`, the rows
`x ↦ H (μ x)`, for the signed map `H` of the rows of `H`, form a parametrized cocycle from
`μ.comp ν₀` to `μ.comp ν₁`. -/
def RowFiniteParametrizedCocycle.whiskerLeft (hA : IsDGAlgebra 𝒜 d)
    (μ : RowFiniteContinuationCocycle mS mP) {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}
    (H : RowFiniteParametrizedCocycle ν₀ ν₁) :
    RowFiniteParametrizedCocycle (μ.comp ν₀ hA) (μ.comp ν₁ hA) :=
  ofRowFiniteHomDifferential (fun x ↦ rowFiniteSignedMap 𝒜 1 H.h (μ.ν x))
    (fun x ↦ by
      convert H.rowFiniteSignedMap_mem_totalGrading (μ.ν_mem_rowFiniteTotalGrading x) using 2
      ring)
    (by
      rw [← rowFiniteSignedMap_neg_one,
        μ.rowFiniteHomDifferential_comp (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA),
        H.rowFiniteHomDifferential_h]
      funext x
      simp [rowFiniteSignedMap_zero_left, Finsupp.linearCombination_apply, smul_sub,
        Finsupp.sum_sub])

@[simp]
theorem RowFiniteParametrizedCocycle.whiskerLeft_h (hA : IsDGAlgebra 𝒜 d)
    (μ : RowFiniteContinuationCocycle mS mP) {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}
    (H : RowFiniteParametrizedCocycle ν₀ ν₁) (x : S) :
    (H.whiskerLeft hA μ).h x = rowFiniteSignedMap 𝒜 1 H.h (μ.ν x) :=
  (rfl)

end FreeTarget

namespace RowFiniteTwistingCocycle

variable {P : Type uP} {ind : P → ℤ} (m : RowFiniteTwistingCocycle 𝒜 d P ind)
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {𝒩' : ℤ → Submodule R N'} [SetLike.GradedSMul 𝒜 𝒩'] [DirectSum.Decomposition 𝒩']
  {dN : N →ₗ[R] N} {dN' : N' →ₗ[R] N'}

/-! ### One generator at a time -/

section Step

variable (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (φ : N →ₗ[A] N')
  (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
  (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
  {k : ℤ} {c : P → N} {w : P → N'} (hc : ∀ x, c x ∈ 𝒩 (k - ind x))
  (hw : ∀ x, w x ∈ 𝒩' (k - 1 - ind x))
  (hdc : rowFiniteHomDifferential 𝒜 m.m dN k c = 0)
  (hφc : φ ∘ c = rowFiniteHomDifferential 𝒜 m.m dN' (k - 1) w)

/-- Generator values `(U, V)` solve the bounding problem at `x` when they have the right
degrees there and `δ U = c`, `φ ∘ U + δ V = w` hold at `x`. -/
private def IsSolutionAt (k : ℤ) (c : P → N) (w : P → N') (U : P → N) (V : P → N') (x : P) :
    Prop :=
  U x ∈ 𝒩 (k - 1 - ind x) ∧ V x ∈ 𝒩' (k - 2 - ind x) ∧
    rowFiniteHomDifferential 𝒜 m.m dN (k - 1) U x = c x ∧
    φ (U x) + rowFiniteHomDifferential 𝒜 m.m dN' (k - 2) V x = w x

include hN hN' hφ hrel hc hw hdc hφc in
/-- **The step at one generator.** If `(U, V)` solve the bounding problem on the row of `x`, then
the obstruction at `x` is a relative cycle of `φ`, so there are values at `x`, of the right
degrees, which solve it there. -/
private theorem exists_step (U : P → N) (V : P → N') (x : P)
    (hUV : ∀ y ∈ (m.m x).support, IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') φ
      k c w U V y) :
    ∃ u ∈ 𝒩 (k - 1 - ind x), ∃ v ∈ 𝒩' (k - 2 - ind x),
      dN u = c x + (k - 1).negOnePow • rowFiniteSignedMap 𝒜 (k - 1) U (m.m x) ∧
      φ u + dN' v = w x + (k - 2).negOnePow • rowFiniteSignedMap 𝒜 (k - 2) V (m.m x) := by
  have hrow := m.m_mem_rowFiniteTotalGrading x
  have hsign (j : ℤ) : (j - 1).negOnePow = -j.negOnePow := by
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]
  set C := c x + (k - 1).negOnePow • rowFiniteSignedMap 𝒜 (k - 1) U (m.m x)
  set W := w x + (k - 2).negOnePow • rowFiniteSignedMap 𝒜 (k - 2) V (m.m x)
  -- The obstruction `(C, W)` is a relative cycle of `φ`, homogeneous of the right degrees.
  have hC : C ∈ 𝒩 (k - ind x) := by
    refine Submodule.add_mem _ (hc x) (Submodule.smul_of_tower_mem _ _ ?_)
    convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading hrow fun y hy ↦ (hUV y hy).1
      using 2
    ring
  have hW : W ∈ 𝒩' (k - 1 - ind x) := by
    refine Submodule.add_mem _ (hw x) (Submodule.smul_of_tower_mem _ _ ?_)
    convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading hrow fun y hy ↦ (hUV y hy).2.1
      using 2
    ring
  have hdC : dN C = 0 := by
    -- The Leibniz identity on the row of `x`, whose differential vanishes.
    have h₁ := rowFiniteSignedMap_rowFiniteHomDifferential hN m.m (k - 1) U (m.m x)
    rw [m.differential_row, map_zero, smul_zero, sub_zero, sub_add_cancel,
      rowFiniteSignedMap_congr k fun y hy ↦ (hUV y hy).2.2.1] at h₁
    have h₂ := congrFun hdc x
    rw [rowFiniteHomDifferential_apply, Pi.zero_apply] at h₂
    rw [map_add, LinearMap.map_smul_of_tower, ← h₁, hsign, Units.neg_smul, ← sub_eq_add_neg, h₂]
  have hgC : φ C = dN' W := by
    have h₁ := rowFiniteSignedMap_rowFiniteHomDifferential hN' m.m (k - 2) V (m.m x)
    rw [m.differential_row, map_zero, smul_zero, sub_zero, show k - 2 + 1 = k - 1 by ring] at h₁
    have h₂ : rowFiniteSignedMap 𝒜 (k - 1) (w - φ ∘ U) (m.m x) =
        rowFiniteSignedMap 𝒜 (k - 1)
          (rowFiniteHomDifferential 𝒜 m.m dN' (k - 2) V) (m.m x) :=
      rowFiniteSignedMap_congr _ fun y hy ↦ by
        rw [Pi.sub_apply, Function.comp_apply, ← (hUV y hy).2.2.2, add_sub_cancel_left]
    have h₃ := congrFun hφc x
    rw [Function.comp_apply, rowFiniteHomDifferential_apply] at h₃
    rw [map_add, LinearMap.map_smul_of_tower, h₃, LinearMap.map_rowFiniteSignedMap, map_add,
      LinearMap.map_smul_of_tower, ← h₁, ← h₂, rowFiniteSignedMap_sub,
      show k - 2 = k - 1 - 1 by ring, hsign (k - 1), smul_sub]
    simp only [Units.neg_smul]
    abel
  -- Since `φ` is a quasi-isomorphism the obstruction bounds; keep the homogeneous components.
  obtain ⟨u₀, v₀, hu₀, huv₀⟩ := hrel C W hdC hgC
  refine ⟨decompose 𝒩 u₀ (k - 1 - ind x), SetLike.coe_mem _,
    decompose 𝒩' v₀ (k - 2 - ind x), SetLike.coe_mem _, ?_, ?_⟩
  · rw [hN.map_decompose, hu₀, show k - 1 - ind x + 1 = k - ind x by ring,
      decompose_of_mem_same _ hC]
  · rw [hφ.map_decompose, add_zero, hN'.map_decompose,
      show k - 2 - ind x + 1 = k - 1 - ind x by ring,
      ← Submodule.coe_add, ← DirectSum.add_apply, ← decompose_add, huv₀,
      decompose_of_mem_same _ hW]

omit [GradedAlgebra 𝒜] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition 𝒩'] in
/-- The entries of a row of a one-sided cocycle lie in strictly lower levels. -/
private theorem lt_of_mem_support (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y : P}
    (hy : y ∈ (m.m x).support) : ind y < ind x :=
  lt_of_not_ge fun h ↦ Finsupp.mem_support_iff.mp hy (hm x y h)

include hN hN' hφ hrel hc hw hdc hφc in
/-- **Extending a solution by one level.** A solution of the bounding problem on the generators
below level `p₀ + n` extends, keeping its values there, to a solution below level `p₀ + n + 1`:
the generators of level `p₀ + n` are treated independently by `exists_step`. -/
private theorem exists_extend (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) (p₀ : ℤ) (n : ℕ)
    (U : P → N) (V : P → N') :
    ∃ (U' : P → N) (V' : P → N'),
      (∀ x, ind x < p₀ + n → IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') φ
        k c w U V x) →
        (∀ x, ind x < p₀ + n → U' x = U x ∧ V' x = V x) ∧
          ∀ x, ind x < p₀ + n + 1 → IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN)
            (dN' := dN') φ k c w U' V' x := by
  classical
  -- The hypothesis on `(U, V)` sits inside the existential, so that `choose` can extract the
  -- extension as a function of arbitrary stages; when it fails, any witness will do.
  let Sol := IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') φ k c w
  by_cases hsol : ∀ x, ind x < p₀ + n → Sol U V x
  · have hstep : ∀ x, ind x = p₀ + n → _ := fun x hx ↦
      exists_step m hN hN' φ hφ hrel hc hw hdc hφc U V x fun y hy ↦
        hsol y (hx ▸ lt_of_mem_support m hm hy)
    choose u hu v hv hdu hguv using hstep
    let U' : P → N := fun x ↦ if hx : ind x = p₀ + n then u x hx else U x
    let V' : P → N' := fun x ↦ if hx : ind x = p₀ + n then v x hx else V x
    have hU'ne {x : P} (hx : ind x ≠ p₀ + n) : U' x = U x := by simp [U', hx]
    have hV'ne {x : P} (hx : ind x ≠ p₀ + n) : V' x = V x := by simp [V', hx]
    have hU'eq {x : P} (hx : ind x = p₀ + n) : U' x = u x hx := by simp [U', hx]
    have hV'eq {x : P} (hx : ind x = p₀ + n) : V' x = v x hx := by simp [V', hx]
    -- The new values agree with the old ones on every row of the new level.
    have hagree {x : P} (hx : ind x ≤ p₀ + n) {y : P} (hy : y ∈ (m.m x).support) :
        U' y = U y ∧ V' y = V y :=
      have hyx := (lt_of_mem_support m hm hy).trans_le hx
      ⟨hU'ne hyx.ne, hV'ne hyx.ne⟩
    refine ⟨U', V', fun _ ↦ ⟨fun x hx ↦ ⟨hU'ne hx.ne, hV'ne hx.ne⟩, fun x hx ↦ ?_⟩⟩
    rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hx) with hx | hx
    · obtain ⟨hU, hV, hδU, hδV⟩ := hsol x hx
      refine ⟨by rwa [hU'ne hx.ne], by rwa [hV'ne hx.ne], ?_, ?_⟩
      · rw [rowFiniteHomDifferential_congr _ _ _ (hU'ne hx.ne)
          fun y hy ↦ (hagree hx.le hy).1, hδU]
      · rw [rowFiniteHomDifferential_congr _ _ _ (hV'ne hx.ne)
          fun y hy ↦ (hagree hx.le hy).2, hU'ne hx.ne, hδV]
    · refine ⟨by rw [hU'eq hx]; exact hu x hx, by rw [hV'eq hx]; exact hv x hx, ?_, ?_⟩
      · rw [rowFiniteHomDifferential_apply, hU'eq hx, hdu,
          rowFiniteSignedMap_congr _ fun y hy ↦ (hagree hx.le hy).1]
        abel
      · rw [rowFiniteHomDifferential_apply, hU'eq hx, hV'eq hx, add_sub_assoc', hguv,
          rowFiniteSignedMap_congr _ fun y hy ↦ (hagree hx.le hy).2]
        abel
  · exact ⟨U, V, fun h ↦ absurd h hsol⟩

end Step

/-! ### Graded maps out of `K_m` preserve quasi-isomorphisms -/

/-- **Graded maps out of a bounded-below one-sided row-finite free module preserve
quasi-isomorphisms.** Let `φ : N → N'` be a degree-preserving `A`-linear map between differential
graded left modules all of whose relative cycles are relative boundaries: whenever `dN c = 0` and
`φ c = dN' w`, there are `u` and `v` with `dN u = c` and `φ u + dN' v = w`. For a morphism of
differential graded modules this says that `φ` is a quasi-isomorphism, as in
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`. Let `c` and `w` be generator values of
degrees `k` and `k - 1` of graded maps `K_m → N` and `K_m → N'` forming a relative cycle:
`δ c = 0` and `φ ∘ c = δ w`. Then they form a relative boundary: there are generator values `u`
and `v` of degrees `k - 1` and `k - 2` with `δ u = c` and `φ ∘ u + δ v = w`. -/
theorem exists_rowFiniteHomDifferential_eq_of_forall_exists
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (φ : N →ₗ[A] N')
    (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
    (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
    {k : ℤ} {c : P → N} {w : P → N'} (hc : ∀ x, c x ∈ 𝒩 (k - ind x))
    (hw : ∀ x, w x ∈ 𝒩' (k - 1 - ind x))
    (hdc : rowFiniteHomDifferential 𝒜 m.m dN k c = 0)
    (hφc : φ ∘ c = rowFiniteHomDifferential 𝒜 m.m dN' (k - 1) w) :
    ∃ (u : P → N) (v : P → N'), (∀ x, u x ∈ 𝒩 (k - 1 - ind x)) ∧
      (∀ x, v x ∈ 𝒩' (k - 2 - ind x)) ∧ rowFiniteHomDifferential 𝒜 m.m dN (k - 1) u = c ∧
      φ ∘ u + rowFiniteHomDifferential 𝒜 m.m dN' (k - 2) v = w := by
  classical
  let Sol := IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') φ k c w
  -- Extend solutions one level at a time.
  have hext := fun n ↦ exists_extend m hN hN' φ hφ hrel hc hw hdc hφc hm p₀ n
  choose U' V' hUV' using hext
  -- The solutions below successive levels, each extending the previous one.
  let seq : ℕ → (P → N) × (P → N') := fun n ↦
    Nat.rec (0, 0) (fun n s ↦ (U' n s.1 s.2, V' n s.1 s.2)) n
  have hseq_succ (n : ℕ) : seq (n + 1) = (U' n (seq n).1 (seq n).2, V' n (seq n).1 (seq n).2) :=
    (rfl)
  have hsol : ∀ n : ℕ, ∀ x, ind x < p₀ + n → Sol (seq n).1 (seq n).2 x := by
    intro n
    induction n with
    | zero => exact fun x hx ↦ absurd (hp₀ x) (by simpa using hx)
    | succ n ih =>
      rw [hseq_succ]
      exact fun x hx ↦ ((hUV' n _ _ ih).2 x (by simpa [add_assoc] using hx))
  have hmono : ∀ n n' : ℕ, n ≤ n' → ∀ x, ind x < p₀ + n →
      (seq n').1 x = (seq n).1 x ∧ (seq n').2 x = (seq n).2 x := by
    intro n n' hnn'
    induction n', hnn' using Nat.le_induction with
    | base => exact fun _ _ ↦ ⟨rfl, rfl⟩
    | succ n' hnn' ih =>
      intro x hx
      rw [hseq_succ]
      obtain ⟨h₁, h₂⟩ := (hUV' n' _ _ (hsol n')).1 x (hx.trans_le (by omega))
      exact ⟨h₁.trans (ih x hx).1, h₂.trans (ih x hx).2⟩
  -- The limit: the value at `x` is taken from any stage past the level of `x`.
  let level : P → ℕ := fun x ↦ (ind x - p₀).toNat + 1
  have hlevel (x : P) : ind x < p₀ + level x := by simp only [level]; omega
  have hlim {x : P} {n : ℕ} (hn : level x ≤ n) :
      (seq n).1 x = (seq (level x)).1 x ∧ (seq n).2 x = (seq (level x)).2 x :=
    hmono _ _ hn x (hlevel x)
  let u : P → N := fun x ↦ (seq (level x)).1 x
  let v : P → N' := fun x ↦ (seq (level x)).2 x
  -- On a row, `u` and `v` agree with the stage of the generator of the row.
  have hrow {x y : P} (hy : y ∈ (m.m x).support) :
      u y = (seq (level x)).1 y ∧ v y = (seq (level x)).2 y := by
    have hle : level y ≤ level x := by have := lt_of_mem_support m hm hy; simp only [level]; omega
    exact ⟨(hlim hle).1.symm, (hlim hle).2.symm⟩
  have hsolx (x : P) : Sol u v x := by
    obtain ⟨hU, hV, hδU, hδV⟩ := hsol (level x) x (hlevel x)
    refine ⟨hU, hV, ?_, ?_⟩
    · rw [rowFiniteHomDifferential_congr (u := u) (u' := (seq (level x)).1) _ _ _ rfl
        fun y hy ↦ (hrow hy).1, hδU]
    · rw [rowFiniteHomDifferential_congr (u := v) (u' := (seq (level x)).2) _ _ _ rfl
        fun y hy ↦ (hrow hy).2, hδV]
  exact ⟨u, v, fun x ↦ (hsolx x).1, fun x ↦ (hsolx x).2.1, funext fun x ↦ (hsolx x).2.2.1,
    funext fun x ↦ (hsolx x).2.2.2⟩

/-- Homotopy lifting along a quasi-isomorphism, on generator values: a morphism `K_m → N'` with
generator values `g` lifts along `φ` to a morphism with generator values `ĝ`, up to a homotopy
`k` of degree `-1` with `φ ∘ ĝ + δ k = g`. This is the degree `1` case of
`exists_rowFiniteHomDifferential_eq_of_forall_exists`. -/
private theorem exists_lift_rowFiniteHomDifferential
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (φ : N →ₗ[A] N')
    (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
    (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
    {g : P → N'} (hg : ∀ x, g x ∈ 𝒩' (-ind x))
    (hgd : ∀ x, Finsupp.linearCombination A g (m.m x) = dN' (g x)) :
    ∃ ĝ : P → N, (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧
      (∀ x, Finsupp.linearCombination A ĝ (m.m x) = dN (ĝ x)) ∧
      ∃ k : P → N', (∀ x, k x ∈ 𝒩' (-1 - ind x)) ∧
        φ ∘ ĝ + rowFiniteHomDifferential 𝒜 m.m dN' (-1) k = g := by
  obtain ⟨ĝ, k, hĝ, hk, hĝd, hφĝ⟩ := m.exists_rowFiniteHomDifferential_eq_of_forall_exists hm hp₀
    hN hN' φ hφ hrel (k := 1) (c := 0) (w := g) (fun _ ↦ zero_mem _)
    (fun x ↦ by simpa using hg x)
    (funext fun x ↦ by simp [rowFiniteHomDifferential_apply])
    (by
      rw [show (1 : ℤ) - 1 = 0 by norm_num,
        (forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (𝒜 := 𝒜) m.m g).mp hgd]
      exact funext fun x ↦ by simp)
  refine ⟨ĝ, fun x ↦ by simpa using hĝ x, ?_, k, fun x ↦ by simpa using hk x, ?_⟩
  · rw [forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (𝒜 := 𝒜)]
    simpa using hĝd
  · simpa using hφĝ

/-- **A morphism which becomes null-homotopic after a quasi-isomorphism is null-homotopic.**
Under the hypotheses of `exists_rowFiniteHomDifferential_eq_of_forall_exists`, let `ψ` be the
generator values of a morphism `K_m → N` of differential graded left modules whose composite with
`φ` is null-homotopic, `φ ∘ ψ = δ η`. Then `ψ` itself is null-homotopic: `ψ = δ θ` for a homotopy
`θ` of degree `-1`. -/
theorem exists_nullHomotopy_of_forall_exists
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (φ : N →ₗ[A] N')
    (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
    (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
    {ψ : P → N} (hψ : ∀ x, ψ x ∈ 𝒩 (-ind x))
    (hdψ : ∀ x, Finsupp.linearCombination A ψ (m.m x) = dN (ψ x))
    {η : P → N'} (hη : ∀ x, η x ∈ 𝒩' (-1 - ind x))
    (hφψ : φ ∘ ψ = rowFiniteHomDifferential 𝒜 m.m dN' (-1) η) :
    ∃ θ : P → N, (∀ x, θ x ∈ 𝒩 (-1 - ind x)) ∧
      rowFiniteHomDifferential 𝒜 m.m dN (-1) θ = ψ := by
  obtain ⟨θ, -, hθ, -, hδθ, -⟩ := m.exists_rowFiniteHomDifferential_eq_of_forall_exists hm hp₀
    hN hN' φ hφ hrel (k := 0) (c := ψ) (w := η) (fun x ↦ by simpa using hψ x)
    (fun x ↦ by simpa using hη x)
    ((forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (𝒜 := 𝒜) m.m ψ).mp hdψ)
    (by simpa using hφψ)
  exact ⟨θ, fun x ↦ by simpa using hθ x, by simpa using hδθ⟩

/-! ### Lifting along quasi-isomorphisms -/

section Lifting

variable (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
  (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN')
  {φ : N →ₗ[A] N'} (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
  (hφd : ∀ y, φ (dN y) = dN' (φ y))
  (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
  {g : P → N'} (hg : ∀ x, g x ∈ 𝒩' (-ind x))
  (hgd : ∀ x, Finsupp.linearCombination A g (m.m x) = dN' (g x))

include hm hN hN' hφ hrel hg hgd in
/-- **Semi-free modules are K-projective: lifting along quasi-isomorphisms up to homotopy.**
Let `m` be one-sided, with generator indices bounded below, and let `φ : N → N'` be a
degree-preserving `A`-linear map whose relative cycles are relative boundaries: every `(c, w)`
with `dN c = 0` and `φ c = dN' w` is `(dN u, φ u + dN' v)`. For a morphism of DG left modules this
says that `φ` is a quasi-isomorphism. Then every degree-preserving chain map `g : K_m → N'`,
given by the images of the generators, lifts up to homotopy along `φ`: there are a
degree-preserving chain map `ĝ : K_m → N` and a homotopy `H` of degree `-1`, the signed extension
of `k`, with `g - φ ∘ ĝ = dN' ∘ H + H ∘ D`. -/
theorem exists_lift_homotopy {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) :
    ∃ (ĝ : P → N) (k : P → N'), (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧ (∀ x, k x ∈ 𝒩' (-ind x - 1)) ∧
      (∀ f, Finsupp.linearCombination A ĝ
          (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
        dN (Finsupp.linearCombination A ĝ f)) ∧
      ∀ f, Finsupp.linearCombination A g f - φ (Finsupp.linearCombination A ĝ f) =
        dN' (rowFiniteSignedMap 𝒜 1 k f) +
          rowFiniteSignedMap 𝒜 1 k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) := by
  obtain ⟨ĝ, hĝ, hĝd, k, hk, hφĝ⟩ :=
    exists_lift_rowFiniteHomDifferential m hm hp₀ hN hN' φ hφ hrel hg hgd
  -- On generators, the homotopy law is the degree `-1` equation `φ ∘ ĝ + δ k = g`.
  have hgen (x : P) :
      g x - φ (ĝ x) = dN' (k x) + rowFiniteSignedMap 𝒜 1 k (m.m x) := by
    have h := congrFun hφĝ x
    rw [Pi.add_apply, Function.comp_apply, rowFiniteHomDifferential_neg_one_apply] at h
    rw [← h, add_sub_cancel_left]
  refine ⟨ĝ, k, hĝ, fun x ↦ by convert hk x using 2; ring,
    linearCombination_rowFiniteTwistedDifferential hN m.m hĝd, fun f ↦ ?_⟩
  rw [← linearCombination_eq_add_rowFiniteSignedMap hN' m.m (e := fun y ↦ g y - φ (ĝ y)) hgen f]
  simp [Finsupp.linearCombination_apply, smul_sub, Finsupp.sum_sub, map_finsuppSum]

include hm hN in
/-- **Semi-free modules are K-projective: maps into acyclic modules are null-homotopic.** Let
`m` be one-sided, with generator indices bounded below, and let `N` be an acyclic DG left
module: every cycle is a boundary. Then every degree-preserving chain map `g : K_m → N` is
null-homotopic: `g = dN ∘ H + H ∘ D` for the signed extension `H` of some `k` of degree `-1`. -/
theorem exists_nullHomotopy {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hacyc : ∀ c, dN c = 0 → ∃ u, dN u = c) {g : P → N} (hg : ∀ x, g x ∈ 𝒩 (-ind x))
    (hgd : ∀ x, Finsupp.linearCombination A g (m.m x) = dN (g x)) :
    ∃ k : P → N, (∀ x, k x ∈ 𝒩 (-ind x - 1)) ∧
      ∀ f, Finsupp.linearCombination A g f = dN (rowFiniteSignedMap 𝒜 1 k f) +
        rowFiniteSignedMap 𝒜 1 k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) := by
  obtain ⟨_, k, _, hk, _, hgk⟩ := exists_lift_homotopy m hm hN hN
    (LinearMap.isHomogeneous_zero 𝒩 𝒩 0) (φ := 0)
    (fun c w hc hw ↦ by
      obtain ⟨u, hu⟩ := hacyc c hc
      obtain ⟨v, hv⟩ := hacyc w (by simpa using hw.symm)
      exact ⟨u, v, hu, by simpa using hv⟩) hg hgd hp₀
  exact ⟨k, hk, fun f ↦ by simpa using hgk f⟩

include hm hN hN' hφ hφd hrel hg hgd in
/-- **Semi-free modules are cofibrant: strict lifting along surjective quasi-isomorphisms.** Let
`m` be one-sided, with generator indices bounded below, and let `φ : N → N'` be a surjective
degree-preserving quasi-isomorphism of DG left modules. Then every degree-preserving chain map
`g : K_m → N'` factors through `φ` as a degree-preserving chain map `ĝ : K_m → N`. -/
theorem exists_lift {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) (hφs : Function.Surjective φ) :
    ∃ ĝ : P → N, (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧
      (∀ f, Finsupp.linearCombination A ĝ
          (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
        dN (Finsupp.linearCombination A ĝ f)) ∧
      ∀ f, φ (Finsupp.linearCombination A ĝ f) = Finsupp.linearCombination A g f := by
  classical
  obtain ⟨ĝ, k, hĝ, hk, hĝd, hgk⟩ := exists_lift_homotopy m hm hN hN' hφ hrel hg hgd hp₀
  -- Lift the homotopy to `N`, in the same degrees.
  have hlift (x : P) : ∃ l : N, l ∈ 𝒩 (-ind x - 1) ∧ φ l = k x := by
    obtain ⟨l, hl⟩ := hφs (k x)
    refine ⟨DirectSum.decompose 𝒩 l (-ind x - 1), SetLike.coe_mem _, ?_⟩
    rw [hφ.map_decompose, add_zero, hl, DirectSum.decompose_of_mem_same _ (hk x)]
  choose l hl hφl using hlift
  have hφk : φ ∘ l = k := funext hφl
  -- Correct the lift by the null-homotopic map `dN ∘ L + L ∘ D`, where `L` lifts the homotopy.
  let e (x : P) : N := dN (l x) + rowFiniteSignedMap 𝒜 1 l (m.m x)
  have he (f : P →₀ A) :
      Finsupp.linearCombination A e f = dN (rowFiniteSignedMap 𝒜 1 l f) +
        rowFiniteSignedMap 𝒜 1 l (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) :=
    linearCombination_eq_add_rowFiniteSignedMap hN m.m (fun _ ↦ rfl) f
  have hsum (f : P →₀ A) :
      Finsupp.linearCombination A (ĝ + e) f =
        Finsupp.linearCombination A ĝ f + Finsupp.linearCombination A e f := by
    simp [Finsupp.linearCombination_apply, smul_add, Finsupp.sum_add]
  have hφS (f : P →₀ A) :
      φ (rowFiniteSignedMap 𝒜 1 l f) = rowFiniteSignedMap 𝒜 1 k f := by
    rw [LinearMap.map_rowFiniteSignedMap, hφk]
  refine ⟨ĝ + e, fun x ↦ add_mem (hĝ x) (add_mem ?_ ?_), fun f ↦ ?_, fun f ↦ ?_⟩
  · convert hN.isHomogeneous.map_mem (hl x) using 2
    ring
  · convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading (j := -1)
      (m.m_mem_rowFiniteTotalGrading x) (fun y _ ↦ by convert hl y using 2; ring) using 2
    ring
  · rw [hsum, hsum, hĝd, he, he, m.differential_sq_zero hA, map_zero, add_zero]
    simp only [map_add, hN.sq_zero, zero_add]
  · rw [hsum, map_add, he, map_add, hφd, hφS, hφS, ← hgk f]
    abel

end Lifting

end RowFiniteTwistingCocycle

/-! ### Quasi-isomorphisms of semi-free modules are homotopy equivalences -/

namespace RowFiniteContinuationCocycle

variable {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}

/-- **A quasi-isomorphism of bounded-below one-sided row-finite semi-free modules is a homotopy
equivalence.** Let `ν` be a continuation cocycle from `mP` to `mQ`, both one-sided with generator
indices bounded below, whose morphism `K_mP → K_mQ` of free differential graded left modules is a
quasi-isomorphism in the elementwise sense. Then `ν` is part of a homotopy equivalence of twisting
cocycles: `mP` and `mQ` are homologous through `ν`. In particular
`TauCeti.RowFiniteHomologous.homotopyEquiv` makes the twisted complexes with coefficients in any
differential graded right module homotopy equivalent through the coefficient continuation map of
`ν`. -/
theorem exists_rowFiniteHomologous_of_forall_exists (ν : RowFiniteContinuationCocycle mP mQ)
    (hmP : ∀ x y, indP x ≤ indP y → mP.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ indP x)
    (hmQ : ∀ x y, indQ x ≤ indQ y → mQ.m x y = 0) {q₀ : ℤ} (hq₀ : ∀ y, q₀ ≤ indQ y)
    (hν : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      Finsupp.linearCombination A ν.ν c = rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m w →
      ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
        Finsupp.linearCombination A ν.ν u + rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m v =
          w) :
    ∃ H : RowFiniteHomologous hA mP mQ, H.ν = ν := by
  classical
  have hP := mP.isDGLeftModule_rowFiniteTwistedDifferential hA
  have hQ := mQ.isDGLeftModule_rowFiniteTwistedDifferential hA
  set g : (P →₀ A) →ₗ[A] (Q →₀ A) := Finsupp.linearCombination A ν.ν with hgdef
  have hg₀ : LinearMap.IsHomogeneous g (rowFiniteTotalGrading 𝒜 indP)
      (rowFiniteTotalGrading 𝒜 indQ) 0 := LinearMap.isHomogeneous_def.mpr fun _ _ hz ↦ by
    simpa using ν.linearCombination_mem_totalGrading hz
  -- A homotopy inverse `κ` of `ν`, lifting the identity of `K_mQ` along `ν`.
  obtain ⟨κ, hκ, hdκ, η, hη, hgκ⟩ :=
    RowFiniteTwistingCocycle.exists_lift_rowFiniteHomDifferential mQ hmQ hq₀ hP hQ g hg₀ hν
      (refl mQ hA).ν_mem_rowFiniteTotalGrading fun y ↦ ((refl mQ hA).continuation y).symm
  let κ' : RowFiniteContinuationCocycle mQ mP := ofRowFiniteHomDifferential κ hκ
    ((forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mp hdκ)
  -- The homotopy between the identity of `K_mQ` and `ν ∘ κ`.
  let homQ : RowFiniteParametrizedCocycle (refl mQ hA) (κ'.comp ν hA) :=
    .ofRowFiniteHomDifferential (-η) (fun y ↦ neg_mem (hη y)) <| by
      rw [rowFiniteHomDifferential_neg, eq_sub_of_add_eq' hgκ, neg_sub]
      exact congrArg (· - _) (funext fun y ↦ (comp_ν κ' ν hA y).symm)
  -- The composite `κ ∘ ν` becomes null-homotopic after `ν`, hence is homotopic to the identity.
  let homQν := homQ.whiskerLeft hA ν
  have hgψ : g ∘ ((ν.comp κ' hA).ν - (refl mP hA).ν) =
      rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m) (-1)
        homQν.h := by
    rw [homQν.rowFiniteHomDifferential_h, comp_refl, ← comp_assoc]
    funext x
    simp [hgdef]
  have hδψ : rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m)
      0 ((ν.comp κ' hA).ν - (refl mP hA).ν) = 0 := by
    rw [rowFiniteHomDifferential_sub, rowFiniteHomDifferential_ν, rowFiniteHomDifferential_ν,
      sub_zero]
  obtain ⟨θ, hθ, hδθ⟩ := mP.exists_nullHomotopy_of_forall_exists hmP hp₀ hP hQ g hg₀ hν
    (fun x ↦ sub_mem ((ν.comp κ' hA).ν_mem_rowFiniteTotalGrading x)
      ((refl mP hA).ν_mem_rowFiniteTotalGrading x))
    ((forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mpr hδψ)
    (fun x ↦ by
      rw [RowFiniteParametrizedCocycle.whiskerLeft_h]
      convert homQ.rowFiniteSignedMap_mem_totalGrading (ν.ν_mem_rowFiniteTotalGrading x) using 2
      ring)
    hgψ
  exact ⟨⟨ν, κ', .ofRowFiniteHomDifferential θ hθ hδθ, homQ⟩, rfl⟩

end RowFiniteContinuationCocycle

end TauCeti
