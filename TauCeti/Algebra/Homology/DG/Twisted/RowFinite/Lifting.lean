/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Hom

/-!
# The lifting property of row-finite semi-free modules

Let `m` be a row-finite twisting cocycle on a graded basis `(P, ind)` which is one-sided,
`m x y = 0` whenever `ind x ≤ ind y`, and whose generator indices are bounded below, as for the
cells of a CW complex. Its free differential graded left module `K_m` is then semi-free, attached
one index at a time, and it is **K-projective**: maps out of it carry quasi-isomorphisms to
quasi-isomorphisms. Precisely, let `g : N → N'` be a quasi-isomorphism of differential graded left
modules, in the elementwise form of `TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`.
Then every relative cycle of the map of complexes of graded maps `Hom(K_m, N) → Hom(K_m, N')`
is a relative boundary
(`TauCeti.RowFiniteTwistingCocycle.exists_rowFiniteHomDifferential_eq_of_forall_exists`). Graded
maps out of `K_m` are written by their generator values, with the differential
`TauCeti.rowFiniteHomDifferential` of `TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Hom`.

The proof builds the bounding maps one index level at a time. On a generator `x`, the
differential of graded maps only reads the generator values on the row of `x`, which lie in
strictly lower levels, so the obstruction at `x` is a relative cycle of `g` itself; since `g` is a
quasi-isomorphism it is a relative boundary, and its homogeneous components give the values at
`x`. Generators of one level do not interact, and the lower bound on the indices starts the
induction.

The two consequences used for maps of differential graded modules are:

* **lifting** (`TauCeti.RowFiniteTwistingCocycle.exists_lift_of_forall_exists`): a morphism
  `K_m → N'` lifts along `g` to a morphism `K_m → N`, up to a homotopy;
* **uniqueness** (`TauCeti.RowFiniteTwistingCocycle.exists_homotopy_of_forall_exists`): a
  morphism `K_m → N` whose composite with `g` is null-homotopic is itself null-homotopic.

Together they show that a quasi-isomorphism between two such semi-free modules, given by a
continuation cocycle, has a homotopy inverse given by a continuation cocycle, so the two twisting
cocycles are homologous
(`TauCeti.RowFiniteContinuationCocycle.exists_rowFiniteHomologous_of_forall_exists`). By
`TauCeti.RowFiniteHomologous.homotopyEquiv`, the twisted complexes `M ⊗ ⟨P⟩` and `M ⊗ ⟨Q⟩` are
then homotopy equivalent for every differential graded right module `M`. With the invariance in
the coefficient module, `TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap`,
this says that the twisted complex computes a derived tensor product: it depends on the
semi-free module only up to quasi-isomorphism. This is how two cellular semi-free resolutions,
such as the Brown models built from different attaching data, are compared.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.exists_rowFiniteHomDifferential_eq_of_forall_exists`:
  graded maps out of `K_m` preserve quasi-isomorphisms, elementwise.
* `TauCeti.RowFiniteTwistingCocycle.exists_lift_of_forall_exists`: homotopy lifting of morphisms
  out of `K_m` along a quasi-isomorphism.
* `TauCeti.RowFiniteTwistingCocycle.exists_homotopy_of_forall_exists`: a morphism out of `K_m`
  which becomes null-homotopic after a quasi-isomorphism is null-homotopic.
* `TauCeti.RowFiniteContinuationCocycle.exists_rowFiniteHomologous_of_forall_exists`: a
  quasi-isomorphism of such semi-free modules is part of a homotopy equivalence of twisting
  cocycles.

## References

* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational homotopy theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open DirectSum

namespace TauCeti

universe uR uA uN uN' uP uQ

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
    rowFiniteHomDifferential 𝒜 mP.m dN j (fun x ↦ rowFiniteSignedCombination 𝒜 j u (ν.ν x)) =
      fun x ↦ rowFiniteSignedCombination 𝒜 (j + 1) (rowFiniteHomDifferential 𝒜 mQ.m dN j u)
        (ν.ν x) := by
  funext x
  rw [rowFiniteSignedCombination_rowFiniteHomDifferential hN, ν.continuation,
    rowFiniteSignedCombination_linearCombination, rowFiniteHomDifferential_apply]

end Continuation

namespace RowFiniteTwistingCocycle

variable {P : Type uP} {ind : P → ℤ} (m : RowFiniteTwistingCocycle 𝒜 d P ind)
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {𝒩' : ℤ → Submodule R N'} [SetLike.GradedSMul 𝒜 𝒩'] [DirectSum.Decomposition 𝒩']
  {dN : N →ₗ[R] N} {dN' : N' →ₗ[R] N'}

/-! ### One generator at a time -/

section Step

variable (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (g : N →ₗ[A] N')
  (hg₀ : ∀ ⦃n : ℤ⦄ ⦃z : N⦄, z ∈ 𝒩 n → g z ∈ 𝒩' n)
  (hg : ∀ c w, dN c = 0 → g c = dN' w → ∃ u v, dN u = c ∧ g u + dN' v = w)
  {k : ℤ} {c : P → N} {w : P → N'} (hc : ∀ x, c x ∈ 𝒩 (k - ind x))
  (hw : ∀ x, w x ∈ 𝒩' (k - 1 - ind x))
  (hdc : rowFiniteHomDifferential 𝒜 m.m dN k c = 0)
  (hgc : g ∘ c = rowFiniteHomDifferential 𝒜 m.m dN' (k - 1) w)

/-- Generator values `(U, V)` solve the bounding problem at `x` when they have the right
degrees there and `δ U = c`, `g ∘ U + δ V = w` hold at `x`. -/
private def IsSolutionAt (k : ℤ) (c : P → N) (w : P → N') (U : P → N) (V : P → N') (x : P) :
    Prop :=
  U x ∈ 𝒩 (k - 1 - ind x) ∧ V x ∈ 𝒩' (k - 2 - ind x) ∧
    rowFiniteHomDifferential 𝒜 m.m dN (k - 1) U x = c x ∧
    g (U x) + rowFiniteHomDifferential 𝒜 m.m dN' (k - 2) V x = w x

include hN hN' hg₀ hg hc hw hdc hgc in
/-- **The step at one generator.** If `(U, V)` solve the bounding problem on the row of `x`, then
the obstruction at `x` is a relative cycle of `g`, so there are values at `x`, of the right
degrees, which solve it there. -/
private theorem exists_step (U : P → N) (V : P → N') (x : P)
    (hUV : ∀ y ∈ (m.m x).support, IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') g
      k c w U V y) :
    ∃ u ∈ 𝒩 (k - 1 - ind x), ∃ v ∈ 𝒩' (k - 2 - ind x),
      dN u = c x + (k - 1).negOnePow • rowFiniteSignedCombination 𝒜 (k - 1) U (m.m x) ∧
      g u + dN' v = w x + (k - 2).negOnePow • rowFiniteSignedCombination 𝒜 (k - 2) V (m.m x) := by
  have hrow := m.m_mem_rowFiniteTotalGrading x
  have hsign (j : ℤ) : (j - 1).negOnePow = -j.negOnePow := by
    rw [Int.negOnePow_sub, Int.negOnePow_one, mul_neg, mul_one]
  set C := c x + (k - 1).negOnePow • rowFiniteSignedCombination 𝒜 (k - 1) U (m.m x)
  set W := w x + (k - 2).negOnePow • rowFiniteSignedCombination 𝒜 (k - 2) V (m.m x)
  -- The obstruction `(C, W)` is a relative cycle of `g`, homogeneous of the right degrees.
  have hC : C ∈ 𝒩 (k - ind x) := by
    refine Submodule.add_mem _ (hc x) (Submodule.smul_of_tower_mem _ _ ?_)
    convert rowFiniteSignedCombination_mem hrow fun y hy ↦ (hUV y hy).1 using 2
    ring
  have hW : W ∈ 𝒩' (k - 1 - ind x) := by
    refine Submodule.add_mem _ (hw x) (Submodule.smul_of_tower_mem _ _ ?_)
    convert rowFiniteSignedCombination_mem hrow fun y hy ↦ (hUV y hy).2.1 using 2
    ring
  have hdC : dN C = 0 := by
    -- The Leibniz identity on the row of `x`, whose differential vanishes.
    have h₁ := rowFiniteSignedCombination_rowFiniteHomDifferential hN m.m (k - 1) U (m.m x)
    rw [m.differential_row, map_zero, smul_zero, sub_zero, sub_add_cancel,
      rowFiniteSignedCombination_congr k fun y hy ↦ (hUV y hy).2.2.1] at h₁
    have h₂ := congrFun hdc x
    rw [rowFiniteHomDifferential_apply, Pi.zero_apply] at h₂
    rw [map_add, LinearMap.map_smul_of_tower, ← h₁, hsign, Units.neg_smul, ← sub_eq_add_neg, h₂]
  have hgC : g C = dN' W := by
    have h₁ := rowFiniteSignedCombination_rowFiniteHomDifferential hN' m.m (k - 2) V (m.m x)
    rw [m.differential_row, map_zero, smul_zero, sub_zero, show k - 2 + 1 = k - 1 by ring] at h₁
    have h₂ : rowFiniteSignedCombination 𝒜 (k - 1) (w - g ∘ U) (m.m x) =
        rowFiniteSignedCombination 𝒜 (k - 1)
          (rowFiniteHomDifferential 𝒜 m.m dN' (k - 2) V) (m.m x) :=
      rowFiniteSignedCombination_congr _ fun y hy ↦ by
        rw [Pi.sub_apply, Function.comp_apply, ← (hUV y hy).2.2.2, add_sub_cancel_left]
    have h₃ := congrFun hgc x
    rw [Function.comp_apply, rowFiniteHomDifferential_apply] at h₃
    rw [map_add, LinearMap.map_smul_of_tower, h₃, map_rowFiniteSignedCombination, map_add,
      LinearMap.map_smul_of_tower, ← h₁, ← h₂, rowFiniteSignedCombination_sub,
      show k - 2 = k - 1 - 1 by ring, hsign (k - 1), smul_sub]
    simp only [Units.neg_smul]
    abel
  -- Since `g` is a quasi-isomorphism the obstruction bounds; keep the homogeneous components.
  obtain ⟨u₀, v₀, hu₀, huv₀⟩ := hg C W hdC hgC
  refine ⟨decompose 𝒩 u₀ (k - 1 - ind x), SetLike.coe_mem _,
    decompose 𝒩' v₀ (k - 2 - ind x), SetLike.coe_mem _, ?_, ?_⟩
  · rw [hN.map_decompose, hu₀, show k - 1 - ind x + 1 = k - ind x by ring,
      decompose_of_mem_same _ hC]
  · have hgdec : g (decompose 𝒩 u₀ (k - 1 - ind x) : N) =
        (decompose 𝒩' (g u₀) (k - 1 - ind x) : N') :=
      DirectSum.map_decompose_shift 𝒩 𝒩' (g.restrictScalars R).toAddMonoidHom id
        Function.injective_id (fun _ _ hz ↦ hg₀ hz) _ u₀
    rw [hgdec, hN'.map_decompose, show k - 2 - ind x + 1 = k - 1 - ind x by ring,
      ← Submodule.coe_add, ← DirectSum.add_apply, ← decompose_add, huv₀,
      decompose_of_mem_same _ hW]

omit [GradedAlgebra 𝒜] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition 𝒩'] in
/-- The entries of a row of a one-sided cocycle lie in strictly lower levels. -/
private theorem lt_of_mem_support (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {x y : P}
    (hy : y ∈ (m.m x).support) : ind y < ind x :=
  lt_of_not_ge fun h ↦ Finsupp.mem_support_iff.mp hy (hm x y h)

include hN hN' hg₀ hg hc hw hdc hgc in
/-- **Extending a solution by one level.** A solution of the bounding problem on the generators
below level `p₀ + n` extends, keeping its values there, to a solution below level `p₀ + n + 1`:
the generators of level `p₀ + n` are treated independently by `exists_step`. -/
private theorem exists_extend (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) (p₀ : ℤ) (n : ℕ)
    (U : P → N) (V : P → N') :
    ∃ (U' : P → N) (V' : P → N'),
      (∀ x, ind x < p₀ + n → IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') g
        k c w U V x) →
        (∀ x, ind x < p₀ + n → U' x = U x ∧ V' x = V x) ∧
          ∀ x, ind x < p₀ + n + 1 → IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN)
            (dN' := dN') g k c w U' V' x := by
  classical
  let Sol := IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') g k c w
  by_cases hsol : ∀ x, ind x < p₀ + n → Sol U V x
  · have hstep : ∀ x, ind x = p₀ + n → _ := fun x hx ↦
      exists_step m hN hN' g hg₀ hg hc hw hdc hgc U V x fun y hy ↦
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
          rowFiniteSignedCombination_congr _ fun y hy ↦ (hagree hx.le hy).1]
        abel
      · rw [rowFiniteHomDifferential_apply, hU'eq hx, hV'eq hx, add_sub_assoc', hguv,
          rowFiniteSignedCombination_congr _ fun y hy ↦ (hagree hx.le hy).2]
        abel
  · exact ⟨U, V, fun h ↦ absurd h hsol⟩

end Step

/-! ### Graded maps out of `K_m` preserve quasi-isomorphisms -/

/-- **Graded maps out of a bounded-below one-sided row-finite free module preserve
quasi-isomorphisms.** Let `g : N → N'` be a degree-preserving `A`-linear map between differential
graded left modules all of whose relative cycles are relative boundaries: whenever `dN c = 0` and
`g c = dN' w`, there are `u` and `v` with `dN u = c` and `g u + dN' v = w`. For a morphism of
differential graded modules this says that `g` is a quasi-isomorphism, as in
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`. Let `c` and `w` be generator values of
degrees `k` and `k - 1` of graded maps `K_m → N` and `K_m → N'` forming a relative cycle:
`δ c = 0` and `g ∘ c = δ w`. Then they form a relative boundary: there are generator values `u`
and `v` of degrees `k - 1` and `k - 2` with `δ u = c` and `g ∘ u + δ v = w`. -/
theorem exists_rowFiniteHomDifferential_eq_of_forall_exists
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (g : N →ₗ[A] N')
    (hg₀ : ∀ ⦃n : ℤ⦄ ⦃z : N⦄, z ∈ 𝒩 n → g z ∈ 𝒩' n)
    (hg : ∀ c w, dN c = 0 → g c = dN' w → ∃ u v, dN u = c ∧ g u + dN' v = w)
    {k : ℤ} {c : P → N} {w : P → N'} (hc : ∀ x, c x ∈ 𝒩 (k - ind x))
    (hw : ∀ x, w x ∈ 𝒩' (k - 1 - ind x))
    (hdc : rowFiniteHomDifferential 𝒜 m.m dN k c = 0)
    (hgc : g ∘ c = rowFiniteHomDifferential 𝒜 m.m dN' (k - 1) w) :
    ∃ (u : P → N) (v : P → N'), (∀ x, u x ∈ 𝒩 (k - 1 - ind x)) ∧
      (∀ x, v x ∈ 𝒩' (k - 2 - ind x)) ∧ rowFiniteHomDifferential 𝒜 m.m dN (k - 1) u = c ∧
      g ∘ u + rowFiniteHomDifferential 𝒜 m.m dN' (k - 2) v = w := by
  classical
  let Sol := IsSolutionAt m (𝒩 := 𝒩) (𝒩' := 𝒩') (dN := dN) (dN' := dN') g k c w
  -- Extend solutions one level at a time.
  have hext := fun n ↦ exists_extend m hN hN' g hg₀ hg hc hw hdc hgc hm p₀ n
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

/-- **Homotopy lifting along a quasi-isomorphism.** Under the hypotheses of
`exists_rowFiniteHomDifferential_eq_of_forall_exists`, every morphism `K_m → N'` of differential
graded left modules, given by its generator values `φ`, lifts along `g` up to homotopy: there is
a morphism `K_m → N`, with generator values `ψ`, and a homotopy `η` of degree `-1` with
`g ∘ ψ + δ η = φ`. -/
theorem exists_lift_of_forall_exists
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (g : N →ₗ[A] N')
    (hg₀ : ∀ ⦃n : ℤ⦄ ⦃z : N⦄, z ∈ 𝒩 n → g z ∈ 𝒩' n)
    (hg : ∀ c w, dN c = 0 → g c = dN' w → ∃ u v, dN u = c ∧ g u + dN' v = w)
    {φ : P → N'} (hφ : ∀ x, φ x ∈ 𝒩' (-ind x))
    (hdφ : ∀ x, Finsupp.linearCombination A φ (m.m x) = dN' (φ x)) :
    ∃ ψ : P → N, (∀ x, ψ x ∈ 𝒩 (-ind x)) ∧
      (∀ x, Finsupp.linearCombination A ψ (m.m x) = dN (ψ x)) ∧
      ∃ η : P → N', (∀ x, η x ∈ 𝒩' (-1 - ind x)) ∧
        g ∘ ψ + rowFiniteHomDifferential 𝒜 m.m dN' (-1) η = φ := by
  obtain ⟨ψ, η, hψ, hη, hδψ, hgψ⟩ := m.exists_rowFiniteHomDifferential_eq_of_forall_exists hm hp₀
    hN hN' g hg₀ hg (k := 1) (c := 0) (w := φ) (fun _ ↦ zero_mem _)
    (fun x ↦ by simpa using hφ x)
    (funext fun x ↦ by simp [rowFiniteHomDifferential_apply])
    (by
      rw [show (1 : ℤ) - 1 = 0 by norm_num,
        (forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (𝒜 := 𝒜) m.m φ).mp hdφ]
      exact funext fun x ↦ by simp)
  refine ⟨ψ, fun x ↦ by simpa using hψ x, ?_, η, fun x ↦ by simpa using hη x, ?_⟩
  · rw [forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (𝒜 := 𝒜)]
    simpa using hδψ
  · simpa using hgψ

/-- **A morphism which becomes null-homotopic after a quasi-isomorphism is null-homotopic.**
Under the hypotheses of `exists_rowFiniteHomDifferential_eq_of_forall_exists`, let `ψ` be the
generator values of a morphism `K_m → N` of differential graded left modules whose composite with
`g` is null-homotopic, `g ∘ ψ = δ η`. Then `ψ` itself is null-homotopic: `ψ = δ θ` for a homotopy
`θ` of degree `-1`. -/
theorem exists_homotopy_of_forall_exists
    (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN') (g : N →ₗ[A] N')
    (hg₀ : ∀ ⦃n : ℤ⦄ ⦃z : N⦄, z ∈ 𝒩 n → g z ∈ 𝒩' n)
    (hg : ∀ c w, dN c = 0 → g c = dN' w → ∃ u v, dN u = c ∧ g u + dN' v = w)
    {ψ : P → N} (hψ : ∀ x, ψ x ∈ 𝒩 (-ind x))
    (hdψ : ∀ x, Finsupp.linearCombination A ψ (m.m x) = dN (ψ x))
    {η : P → N'} (hη : ∀ x, η x ∈ 𝒩' (-1 - ind x))
    (hgψ : g ∘ ψ = rowFiniteHomDifferential 𝒜 m.m dN' (-1) η) :
    ∃ θ : P → N, (∀ x, θ x ∈ 𝒩 (-1 - ind x)) ∧
      rowFiniteHomDifferential 𝒜 m.m dN (-1) θ = ψ := by
  obtain ⟨θ, -, hθ, -, hδθ, -⟩ := m.exists_rowFiniteHomDifferential_eq_of_forall_exists hm hp₀
    hN hN' g hg₀ hg (k := 0) (c := ψ) (w := η) (fun x ↦ by simpa using hψ x)
    (fun x ↦ by simpa using hη x)
    ((forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero (𝒜 := 𝒜) m.m ψ).mp hdψ)
    (by simpa using hgψ)
  exact ⟨θ, fun x ↦ by simpa using hθ x, by simpa using hδθ⟩

end RowFiniteTwistingCocycle

/-! ### Quasi-isomorphisms of semi-free modules are homotopy equivalences -/

/-- A generator lies in the total degree opposite to its index. -/
private theorem single_one_mem_rowFiniteTotalGrading {P : Type uP} {ind : P → ℤ} (x : P) :
    Finsupp.single x (1 : A) ∈ rowFiniteTotalGrading 𝒜 ind (-ind x) := by
  classical
  rw [mem_rowFiniteTotalGrading_iff]
  intro y
  by_cases hxy : x = y
  · subst y
    simpa using SetLike.one_mem_graded 𝒜
  · simp [Finsupp.single_eq_of_ne (Ne.symm hxy)]

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
  have hg₀ : ∀ ⦃n : ℤ⦄ ⦃z : P →₀ A⦄, z ∈ rowFiniteTotalGrading 𝒜 indP n →
      g z ∈ rowFiniteTotalGrading 𝒜 indQ n := fun _ _ hz ↦ ν.linearCombination_mem_totalGrading hz
  have hsingle (y : Q) := single_one_mem_rowFiniteTotalGrading (𝒜 := 𝒜) (ind := indQ) y
  -- A homotopy inverse `κ` of `ν`, lifting the identity of `K_mQ` along `ν`.
  obtain ⟨κ, hκ, hdκ, η, hη, hgκ⟩ := mQ.exists_lift_of_forall_exists hmQ hq₀ hP hQ g hg₀ hν
    (φ := fun y ↦ Finsupp.single y 1) hsingle fun y ↦ by
      rw [← funext (refl_ν mQ hA)]
      simpa only [refl_ν] using ((RowFiniteContinuationCocycle.refl mQ hA).continuation y).symm
  let κ' : RowFiniteContinuationCocycle mQ mP :=
    { ν := κ
      mem_graded := fun y x ↦ by
        have := (mem_rowFiniteTotalGrading_iff _ _).mp (hκ y) x
        convert this using 2
        ring
      continuation := fun y ↦ (hdκ y).symm }
  have hκ'ν : κ'.ν = κ := rfl
  -- The homotopy between `ν ∘ κ` and the identity of `K_mQ`.
  have homQ : RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mQ hA)
      (κ'.comp ν hA) :=
    { h := -η
      mem_graded := fun y z ↦ by
        have := (mem_rowFiniteTotalGrading_iff _ _).mp (hη y) z
        rw [Pi.neg_apply, Finsupp.neg_apply]
        refine neg_mem ?_
        convert this using 2
        ring
      parametrized := fun y ↦ by
        have h := congrFun hgκ y
        rw [Pi.add_apply, Function.comp_apply, rowFiniteHomDifferential_neg_one_apply,
          rowFiniteSignedCombination_one] at h
        rw [comp_ν, refl_ν, hκ'ν, ← hgdef, ← h, Pi.neg_apply, map_neg,
          ← rowFiniteSignedCombination_one, rowFiniteSignedCombination_neg,
          rowFiniteSignedCombination_one]
        abel }
  -- The composite `κ ∘ ν` becomes null-homotopic after `ν`, hence is homotopic to the identity.
  have hνrow (x : P) : ν.ν x ∈ rowFiniteTotalGrading 𝒜 indQ (-indP x) :=
    (mem_rowFiniteTotalGrading_iff _ _).mpr fun y ↦ by
      convert ν.mem_graded x y using 2
      ring
  have hψ : (ν.comp κ' hA).ν - (RowFiniteContinuationCocycle.refl mP hA).ν =
      fun x ↦ Finsupp.linearCombination A κ (ν.ν x) - Finsupp.single x 1 :=
    funext fun x ↦ by rw [Pi.sub_apply, comp_ν, refl_ν, hκ'ν]
  have hδψ : rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m)
      0 ((ν.comp κ' hA).ν - (RowFiniteContinuationCocycle.refl mP hA).ν) = 0 := by
    rw [rowFiniteHomDifferential_sub,
      (forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mp
        fun x ↦ ((ν.comp κ' hA).continuation x).symm,
      (forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mp
        fun x ↦ ((RowFiniteContinuationCocycle.refl mP hA).continuation x).symm, sub_zero]
  have hgψ : g ∘ ((ν.comp κ' hA).ν - (RowFiniteContinuationCocycle.refl mP hA).ν) =
      rowFiniteHomDifferential 𝒜 mP.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m) (-1)
        (-fun x ↦ rowFiniteSignedCombination 𝒜 (-1) η (ν.ν x)) := by
    have hgκ' : g ∘ κ = (fun y ↦ Finsupp.single y 1) -
        rowFiniteHomDifferential 𝒜 mQ.m (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m)
          (-1) η :=
      eq_sub_of_add_eq hgκ
    rw [rowFiniteHomDifferential_neg, ν.rowFiniteHomDifferential_comp hQ, neg_add_cancel, hψ]
    funext x
    have hid : rowFiniteSignedCombination 𝒜 0 (fun y ↦ Finsupp.single y (1 : A)) (ν.ν x) =
        ν.ν x := by
      rw [rowFiniteSignedCombination_zero_left]
      simp [Finsupp.linearCombination_apply]
    have hgκx : g (Finsupp.linearCombination A κ (ν.ν x)) =
        rowFiniteSignedCombination 𝒜 0 (g ∘ κ) (ν.ν x) := by
      rw [Finsupp.apply_linearCombination, rowFiniteSignedCombination_zero_left,
        LinearMap.restrictScalars_apply]
    have hgs : g (Finsupp.single x 1) = ν.ν x := by
      rw [hgdef, Finsupp.linearCombination_single, one_smul]
    rw [Function.comp_apply, map_sub, hgκx, hgs, hgκ', rowFiniteSignedCombination_sub, hid,
      Pi.neg_apply]
    abel
  have hψmem (x : P) : ((ν.comp κ' hA).ν - (RowFiniteContinuationCocycle.refl mP hA).ν) x ∈
      rowFiniteTotalGrading 𝒜 indP (-indP x) := by
    rw [hψ]
    exact Submodule.sub_mem _ (κ'.linearCombination_mem_totalGrading (hνrow x))
      (single_one_mem_rowFiniteTotalGrading (𝒜 := 𝒜) x)
  have hηmem (x : P) : (-fun x ↦ rowFiniteSignedCombination 𝒜 (-1) η (ν.ν x)) x ∈
      rowFiniteTotalGrading 𝒜 indQ (-1 - indP x) := by
    rw [Pi.neg_apply]
    refine neg_mem ?_
    convert rowFiniteSignedCombination_mem (hνrow x) fun y _ ↦ hη y using 2
    ring
  obtain ⟨θ, hθ, hδθ⟩ := mP.exists_homotopy_of_forall_exists hmP hp₀ hP hQ g hg₀ hν hψmem
    ((forall_linearCombination_eq_iff_rowFiniteHomDifferential_eq_zero _ _).mpr hδψ) hηmem hgψ
  have homP : RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mP hA)
      (ν.comp κ' hA) :=
    { h := θ
      mem_graded := fun x z ↦ by
        have := (mem_rowFiniteTotalGrading_iff _ _).mp (hθ x) z
        convert this using 2
        ring
      parametrized := fun x ↦ by
        have h := congrFun hδθ x
        rwa [rowFiniteHomDifferential_neg_one_apply, rowFiniteSignedCombination_one] at h }
  exact ⟨⟨ν, κ', homP, homQ⟩, rfl⟩

end RowFiniteContinuationCocycle

end TauCeti
