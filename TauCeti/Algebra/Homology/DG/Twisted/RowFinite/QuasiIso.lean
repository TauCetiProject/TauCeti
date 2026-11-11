/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import Mathlib.Logic.Hydra
public import TauCeti.Order.WellFounded.Basic

/-!
# Quasi-isomorphism invariance of row-finite twisted complexes

Let `m` be a row-finite twisting cocycle on a graded basis `(P, ind)` which is **semi-free**: the
relation `y ∈ (m.m x).support`, saying that `y` occurs in the row of `x`, is well-founded. Then a
quasi-isomorphism `f : M → N` of DG right modules induces a quasi-isomorphism
`M ⊗ ⟨P⟩ → N ⊗ ⟨P⟩` of twisted complexes
(`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap`). So the homology of a
twisted complex depends on its DG coefficient module only up to quasi-isomorphism: tensoring with
a semi-free module `K_m` preserves quasi-isomorphisms, that is, semi-free modules are K-flat.

A one-sided cocycle, `m x y = 0` whenever `ind x ≤ ind y`, with generator indices bounded below, as
for the cells of a CW complex or the critical points of a Morse function, is semi-free
(`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support`). The hypothesis also covers semi-free
models whose generator indices are unbounded, such as semi-free resolutions over a DG algebra that
is not concentrated in nonpositive degrees. Through `M ⊗ ⟨P⟩ ≅ M ⊗_A K_m`, it is the invariance of
the derived tensor product `M ⊗^L_A N`, computed from a semi-free resolution `K_m` of `N`, under
quasi-isomorphisms of the first variable.

The proof is a descent along the generators. Write `D` for the twisted differentials. A relative
cycle `(g, k)`, with `D g = 0` and `f g = D k`, is carried by finitely many generators, and since
the row relation is well-founded, one of them, `x`, occurs in the row of none of the others. At
`x` the twisted differential is the module differential alone
(`TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_apply_of_forall_m_eq_zero`), so the
coefficients of `g` and `k` at `x` form a relative cycle of `f`. Since `f` is a quasi-isomorphism it
is a relative boundary (`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`), and subtracting
the corresponding relative boundary leaves a relative cycle carried by the other generators and
by the row of `x`. Replacing a generator by the finitely many generators of its row decreases the
multiset of generators for Mathlib's well-founded order `Relation.CutExpand`, so the descent
terminates. The elementwise criterion
`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap_iff` turns its outcome
into a quasi-isomorphism. No spectral sequence is needed.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.exists_coefficientDifferential_eq_of_forall_exists`: relative
  cycles of the twisted complexes are relative boundaries when this holds for the coefficients.
* `TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap`: a quasi-isomorphism of
  coefficients induces a quasi-isomorphism of semi-free row-finite twisted complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
* B. Keller, *Deriving DG categories*, Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Chapter 6.
-/

public section

open MulOpposite

namespace TauCeti

namespace RowFiniteTwistingCocycle

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M N : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup N] [Module R N] [Module Aᵐᵒᵖ N] [IsScalarTower R Aᵐᵒᵖ N]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {𝒩 : ℤ → Submodule R N} [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece 𝒩]
  {ind : P → ℤ} {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M} {dN : N →ₗ[R] N}
  (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)
  (hN : IsDGRightModule hA 𝒩 dN)

/-! ### Descent along the row relation -/

section Descent

variable (hwf : WellFounded fun y x ↦ y ∈ (m.m x).support)
include hwf

variable (f : DGRightModuleHom hM hN)
  (hf : ∀ c w, dM c = 0 → f c = dN w → ∃ u v, dM u = c ∧ f u + dN v = w)
include hf

/-- One step of the descent: a relative cycle carried by the generators of a multiset `s`
differs from a relative boundary by a relative cycle carried by the generators of a smaller
multiset, obtained by replacing a generator of `s` by the generators of its row. -/
private theorem exists_cutExpand {s : Multiset P} (hs : s ≠ 0) {g : P →₀ M} {k : P →₀ N}
    (hgk₀ : ∀ z ∉ s, g z = 0 ∧ k z = 0) (hg : m.coefficientDifferential hM g = 0)
    (hgk : Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
      m.coefficientDifferential hN k) :
    ∃ (s' : Multiset P) (u : P →₀ M) (v : P →₀ N),
      Relation.CutExpand (fun y x ↦ y ∈ (m.m x).support) s' s ∧
      (∀ z ∉ s', (g - m.coefficientDifferential hM u) z = 0 ∧
        (k - Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u -
          m.coefficientDifferential hN v) z = 0) := by
  classical
  -- Some generator `x` of `s` occurs in the row of no generator of `s`.
  obtain ⟨x₀, hx₀⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨x, hxs, hx⟩ := hwf.exists_mem_forall_not_rel s.toFinset.finite_toSet
    ⟨x₀, Multiset.mem_toFinset.2 hx₀⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset] at hxs
  have hcol {B : Type uM} [AddCommGroup B] {w : P →₀ B} (hw : ∀ z ∉ s, w z = 0) (y : P)
      (hy : w y ≠ 0) : m.m y x = 0 :=
    Finsupp.notMem_support_iff.mp <| hx y <| Finset.mem_coe.2 <| Multiset.mem_toFinset.2 <| by
      by_contra h
      exact hy (hw y h)
  -- The coefficients at `x` are a relative cycle of `f`; bound them.
  have hgx : dM (g x) = 0 := by
    rw [← m.coefficientDifferential_apply_of_forall_m_eq_zero hM
      (hcol (fun z hz ↦ (hgk₀ z hz).1)), hg, Finsupp.zero_apply]
  have hkx : f (g x) = dN (k x) := by
    rw [← m.coefficientDifferential_apply_of_forall_m_eq_zero hN
      (hcol (fun z hz ↦ (hgk₀ z hz).2)), ← hgk]
    simp
  obtain ⟨u₀, v₀, hu₀, huv₀⟩ := hf (g x) (k x) hgx hkx
  -- The differential of an elementary vector at `x`, away from the row of `x`.
  have hD {B : Type uM} [AddCommGroup B] [Module R B] [Module Aᵐᵒᵖ B] [IsScalarTower R Aᵐᵒᵖ B]
      {ℬ : ℤ → Submodule R B} [DirectSum.Decomposition ℬ]
      [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℬ]
      {dB : B →ₗ[R] B} (hB : IsDGRightModule hA ℬ dB) (β : B) {z : P} (hz : m.m x z = 0) :
      m.coefficientDifferential hB (Finsupp.single x β) z = Finsupp.single x (dB β) z := by
    rw [← sub_eq_zero, ← Finsupp.sub_apply]
    exact m.coefficientDifferential_single_sub_apply_of_m_eq_zero hB x β hz
  refine ⟨s.erase x + (m.m x).support.val, Finsupp.single x u₀, Finsupp.single x v₀,
    ⟨(m.m x).support.val, x, fun _ h ↦ Finset.mem_val.mp h, ?_⟩, fun z hz ↦ ?_⟩
  · rw [add_right_comm, add_comm (s.erase x), Multiset.singleton_add, Multiset.cons_erase hxs]
  have hzx : m.m x z = 0 := Finsupp.notMem_support_iff.mp fun h ↦
    hz (Multiset.mem_add.mpr (Or.inr (Finset.mem_val.mpr h)))
  rw [Finsupp.sub_apply, Finsupp.sub_apply, Finsupp.sub_apply, hD hM u₀ hzx, hD hN v₀ hzx]
  by_cases hzx' : z = x
  · subst hzx'
    simp [hu₀, ← huv₀]
  · have hzs : z ∉ s := fun h ↦ hz (Multiset.mem_add.mpr (Or.inl
      ((Multiset.mem_erase_of_ne hzx').mpr h)))
    simp [(hgk₀ z hzs).1, (hgk₀ z hzs).2, Ne.symm hzx']

/-- **Relative cycles of twisted complexes are relative boundaries.** Let `m` be semi-free, and
let `f` be a morphism of DG right modules whose relative cycles are relative boundaries. Then
every relative cycle `(g, k)` of the coefficient maps, with `D g = 0` and `f g = D k`, is a
relative boundary `(D u, f u + D v)`. -/
theorem exists_coefficientDifferential_eq_of_forall_exists {g : P →₀ M} {k : P →₀ N}
    (hg : m.coefficientDifferential hM g = 0)
    (hgk : Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
      m.coefficientDifferential hN k) :
    ∃ (u : P →₀ M) (v : P →₀ N), m.coefficientDifferential hM u = g ∧
      Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u +
        m.coefficientDifferential hN v = k := by
  classical
  -- Well-founded induction on a multiset of generators carrying the relative cycle.
  have hcut : WellFounded (Relation.CutExpand fun y x ↦ y ∈ (m.m x).support) :=
    @WellFounded.cutExpand _ _ hwf
  have key (s : Multiset P) : ∀ (g : P →₀ M) (k : P →₀ N), (∀ z ∉ s, g z = 0 ∧ k z = 0) →
      m.coefficientDifferential hM g = 0 →
      Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
        m.coefficientDifferential hN k →
      ∃ (u : P →₀ M) (v : P →₀ N), m.coefficientDifferential hM u = g ∧
        Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u +
          m.coefficientDifferential hN v = k := by
    induction s using hcut.induction with
    | h s ih =>
      intro g k hgk₀ hg hgk
      by_cases hs : s = 0
      · subst hs
        have hg0 : g = 0 := Finsupp.ext fun z ↦ (hgk₀ z (Multiset.notMem_zero z)).1
        have hk0 : k = 0 := Finsupp.ext fun z ↦ (hgk₀ z (Multiset.notMem_zero z)).2
        exact ⟨0, 0, by simp [hg0], by simp [hk0]⟩
      obtain ⟨s', u, v, hs', hsupp⟩ := m.exists_cutExpand hM hN hwf f hf hs hgk₀ hg hgk
      obtain ⟨u', v', hu', huv'⟩ := ih s' hs' _ _ (fun z hz ↦ hsupp z hz)
        (by rw [map_sub, hg, coefficientDifferential_sq_zero, sub_zero])
        (by rw [map_sub, map_sub, map_sub, hgk, ← m.coefficientDifferential_mapRange hM hN f u,
          coefficientDifferential_sq_zero, sub_zero])
      refine ⟨u + u', v + v', ?_, ?_⟩
      · rw [map_add, hu', add_sub_cancel]
      · rw [map_add, map_add, add_add_add_comm, huv']
        abel
  exact key (g.support.val + k.support.val) g k (fun z hz ↦ by
    simp only [Multiset.mem_add, Finset.mem_val, Finsupp.mem_support_iff, not_or, not_not] at hz
    exact hz) hg hgk

end Descent

/-- **Quasi-isomorphism invariance of twisted complexes.** Let `m` be a semi-free row-finite
twisting cocycle. A quasi-isomorphism `f : M → N` of DG right modules induces a
quasi-isomorphism of the twisted complexes with coefficients in `M` and in `N`. -/
theorem quasiIso_coefficientCochainComplexMap (hwf : WellFounded fun y x ↦ y ∈ (m.m x).support)
    {f : DGRightModuleHom hM hN} (hf : f.IsQuasiIso) :
    QuasiIso (m.coefficientCochainComplexMap hM hN f) := by
  rw [quasiIso_coefficientCochainComplexMap_iff]
  intro n g k hg hk hdg hgk
  obtain ⟨u, v, hu, huv⟩ := m.exists_coefficientDifferential_eq_of_forall_exists hM hN hwf f
    ((DGRightModuleHom.isQuasiIso_iff_forall_exists f).mp hf) hdg hgk
  -- The homogeneous components of `u` and `v` in the matching degrees still work.
  refine ⟨DirectSum.decompose (rowFiniteTotalGrading ℳ ind) u n, SetLike.coe_mem _,
    DirectSum.decompose (rowFiniteTotalGrading 𝒩 ind) v (n - 1), SetLike.coe_mem _, ?_, ?_⟩
  · rw [(m.isHomogeneous_coefficientDifferential hM).map_decompose, hu,
      DirectSum.decompose_of_mem_same _ hg]
  · have hk' := congrArg
      (fun w ↦ (DirectSum.decompose (rowFiniteTotalGrading 𝒩 ind) w n : P →₀ N)) huv
    simp only [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add,
      DirectSum.decompose_of_mem_same _ hk] at hk'
    rw [f.isHomogeneous_mapRange.map_decompose, add_zero,
      (m.isHomogeneous_coefficientDifferential hN).map_decompose, sub_add_cancel]
    exact hk'

end RowFiniteTwistingCocycle

end TauCeti
