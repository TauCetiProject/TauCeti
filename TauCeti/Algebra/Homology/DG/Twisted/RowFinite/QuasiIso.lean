/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Filtration

/-!
# Quasi-isomorphism invariance of row-finite twisted complexes

Let `m` be a row-finite twisting cocycle on a graded basis `(P, ind)` which is one-sided,
`m x y = 0` whenever `ind x ≤ ind y`, and whose generator indices are bounded below, as for the
cells of a CW complex or the critical points of a Morse function. Then a quasi-isomorphism
`f : M → N` of DG right modules induces a quasi-isomorphism `M ⊗ ⟨P⟩ → N ⊗ ⟨P⟩` of twisted
complexes (`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap`). So the
homology of a twisted complex depends on its DG coefficient module only up to
quasi-isomorphism; tensoring with the free module `K_m` preserves quasi-isomorphisms, as for a
semi-free module.

The proof uses the cell filtration by generator index. One-sidedness makes the twisting part of
the coefficient differential strictly lower the index
(`TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_sub_mem_indexFiltration`), so on the
generators of top index the differential is the coefficient differential alone. A relative cycle
`(g, k)`, with `D g = 0` and `f g = D k`, therefore has top-index coefficients which are relative
cycles of `f`. Since `f` is a quasi-isomorphism these are relative boundaries
(`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`), and subtracting the corresponding
relative boundary leaves a relative cycle supported on lower indices. The lower bound on the
indices ends this descent, and the elementwise criterion
`TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap_iff` turns its outcome
into a quasi-isomorphism. No spectral sequence is needed.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.exists_coefficientDifferential_eq_of_forall_exists`: relative
  cycles of the twisted complexes are relative boundaries when this holds for the coefficients.
* `TauCeti.RowFiniteTwistingCocycle.quasiIso_coefficientCochainComplexMap`: a quasi-isomorphism of
  coefficients induces a quasi-isomorphism of row-finite twisted complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
* B. Keller, *Deriving DG categories*, Section 3.
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

/-! ### Relative cycles along the cell filtration -/

section Descent

variable (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0) (f : DGRightModuleHom hM hN)
  (hf : ∀ c w, dM c = 0 → f c = dN w → ∃ u v, dM u = c ∧ f u + dN v = w)
include hm hf

/-- One step of the descent: a relative cycle in the `p`th stage of the cell filtration differs
from a relative boundary by a relative cycle in the `(p - 1)`st stage. -/
private theorem exists_sub_mem_indexFiltration {p : ℤ} {g : P →₀ M} {k : P →₀ N}
    (hgp : g ∈ rowFiniteIndexFiltration (R := R) ind p)
    (hkp : k ∈ rowFiniteIndexFiltration (R := R) ind p) (hg : m.coefficientDifferential hM g = 0)
    (hgk : Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
      m.coefficientDifferential hN k) :
    ∃ (u : P →₀ M) (v : P →₀ N),
      g - m.coefficientDifferential hM u ∈ rowFiniteIndexFiltration (R := R) ind (p - 1) ∧
      k - Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u -
        m.coefficientDifferential hN v ∈ rowFiniteIndexFiltration (R := R) ind (p - 1) := by
  classical
  -- The coefficients on generators of index `p` are relative cycles of `f`.
  have htop (x : P) (hx : ind x = p) : dM (g x) = 0 ∧ f (g x) = dN (k x) := by
    refine ⟨?_, ?_⟩
    · rw [← m.coefficientDifferential_apply_of_eq hM hm hgp hx, hg, Finsupp.zero_apply]
    · rw [← m.coefficientDifferential_apply_of_eq hN hm hkp hx, ← hgk]
      simp
  -- Choose relative boundaries for them, and zero elsewhere.
  have key (x : P) : ∃ (u : M) (v : N), (ind x = p → dM u = g x ∧ f u + dN v = k x) ∧
      ((ind x = p → g x = 0 ∧ k x = 0) → u = 0 ∧ v = 0) := by
    by_cases h : ind x = p → g x = 0 ∧ k x = 0
    · refine ⟨0, 0, fun hx ↦ ?_, fun _ ↦ ⟨rfl, rfl⟩⟩
      obtain ⟨h1, h2⟩ := h hx
      simp [h1, h2]
    · rw [not_imp] at h
      obtain ⟨u, v, hu, huv⟩ := hf (g x) (k x) (htop x h.1).1 (htop x h.1).2
      exact ⟨u, v, fun _ ↦ ⟨hu, huv⟩, fun h' ↦ (h.2 (h' h.1)).elim⟩
  choose U V hUV using key
  have hU0 (x : P) (hx : x ∉ g.support ∪ k.support) : U x = 0 ∧ V x = 0 := by
    simp only [Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hx
    exact (hUV x).2 fun _ ↦ hx
  have hoff (x : P) (hx : ind x ≠ p) : U x = 0 ∧ V x = 0 := (hUV x).2 fun h ↦ absurd h hx
  let u : P →₀ M := Finsupp.onFinset (g.support ∪ k.support) U fun x hx ↦ by
    by_contra h
    exact hx (hU0 x h).1
  let v : P →₀ N := Finsupp.onFinset (g.support ∪ k.support) V fun x hx ↦ by
    by_contra h
    exact hx (hU0 x h).2
  have hu (x : P) : u x = U x := Finsupp.onFinset_apply
  have hv (x : P) : v x = V x := Finsupp.onFinset_apply
  have hup : u ∈ rowFiniteIndexFiltration (R := R) ind p := by
    rw [mem_rowFiniteIndexFiltration_iff ind]
    intro x hx
    rw [hu]
    exact (hoff x (by omega)).1
  have hvp : v ∈ rowFiniteIndexFiltration (R := R) ind p := by
    rw [mem_rowFiniteIndexFiltration_iff ind]
    intro x hx
    rw [hv]
    exact (hoff x (by omega)).2
  have hDu := m.coefficientDifferential_mem_rowFiniteIndexFiltration hM hm hup
  have hDv := m.coefficientDifferential_mem_rowFiniteIndexFiltration hN hm hvp
  refine ⟨u, v, ?_, ?_⟩ <;> rw [mem_rowFiniteIndexFiltration_iff ind] <;> intro x hx <;>
    rcases lt_or_eq_of_le (show p ≤ ind x by omega) with hpx | hpx
  · rw [Finsupp.sub_apply, (mem_rowFiniteIndexFiltration_iff ind).mp hgp x hpx,
      (mem_rowFiniteIndexFiltration_iff ind).mp hDu x hpx, sub_zero]
  · rw [Finsupp.sub_apply, m.coefficientDifferential_apply_of_eq hM hm hup hpx.symm, hu,
      ((hUV x).1 hpx.symm).1, sub_self]
  · simp [(mem_rowFiniteIndexFiltration_iff ind).mp hkp x hpx,
      (mem_rowFiniteIndexFiltration_iff ind).mp hDv x hpx, hu, hoff x hpx.ne']
  · rw [Finsupp.sub_apply, Finsupp.sub_apply,
      m.coefficientDifferential_apply_of_eq hN hm hvp hpx.symm, hv]
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
      LinearMap.coe_restrictScalars, DGRightModuleHom.coe_toLinearMap, hu]
    rw [← ((hUV x).1 hpx.symm).2]
    abel

/-- **Relative cycles of twisted complexes are relative boundaries.** Let `m` be one-sided, with
generator indices bounded below, and let `f` be a morphism of DG right modules whose relative
cycles are relative boundaries. Then every relative cycle `(g, k)` of the coefficient maps, with
`D g = 0` and `f g = D k`, is a relative boundary `(D u, f u + D v)`. -/
theorem exists_coefficientDifferential_eq_of_forall_exists {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x)
    {g : P →₀ M} {k : P →₀ N} (hg : m.coefficientDifferential hM g = 0)
    (hgk : Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
      m.coefficientDifferential hN k) :
    ∃ (u : P →₀ M) (v : P →₀ N), m.coefficientDifferential hM u = g ∧
      Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u +
        m.coefficientDifferential hN v = k := by
  -- Descent on the stage of the cell filtration containing the relative cycle.
  have hdesc (n : ℕ) : ∀ p : ℤ, p < p₀ + n → ∀ (g : P →₀ M) (k : P →₀ N),
      g ∈ rowFiniteIndexFiltration (R := R) ind p →
      k ∈ rowFiniteIndexFiltration (R := R) ind p → m.coefficientDifferential hM g = 0 →
      Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) g =
        m.coefficientDifferential hN k →
      ∃ (u : P →₀ M) (v : P →₀ N), m.coefficientDifferential hM u = g ∧
        Finsupp.mapRange.linearMap (f.toLinearMap.restrictScalars R) u +
          m.coefficientDifferential hN v = k := by
    induction n with
    | zero =>
      intro p hp g k hgp hkp _ _
      have hbot (x : P) : p < ind x := by
        have := hp₀ x
        omega
      rw [rowFiniteIndexFiltration_eq_bot ind hbot, Submodule.mem_bot] at hgp
      rw [rowFiniteIndexFiltration_eq_bot ind hbot, Submodule.mem_bot] at hkp
      exact ⟨0, 0, by simp [hgp], by simp [hkp]⟩
    | succ n ih =>
      intro p hp g k hgp hkp hg hgk
      obtain ⟨u, v, hg', hk'⟩ := m.exists_sub_mem_indexFiltration hM hN hm f hf hgp hkp hg hgk
      obtain ⟨u', v', hu', huv'⟩ := ih (p - 1) (by omega) _ _ hg' hk'
        (by rw [map_sub, hg, coefficientDifferential_sq_zero, sub_zero])
        (by rw [map_sub, map_sub, map_sub, hgk, ← m.coefficientDifferential_mapRange hM hN f u,
          coefficientDifferential_sq_zero, sub_zero])
      refine ⟨u + u', v + v', ?_, ?_⟩
      · rw [map_add, hu', add_sub_cancel]
      · rw [map_add, map_add, add_add_add_comm, huv']
        abel
  -- Both vectors lie in a common stage of the exhaustive cell filtration.
  have hstage {B : Type uM} [AddCommGroup B] [Module R B] (w : P →₀ B) :
      ∃ p, w ∈ rowFiniteIndexFiltration (R := R) ind p := by
    have hw : w ∈ ⨆ p, rowFiniteIndexFiltration (R := R) (A := B) ind p := by
      rw [iSup_rowFiniteIndexFiltration_eq_top]
      exact Submodule.mem_top
    exact (Submodule.mem_iSup_of_directed _ (rowFiniteIndexFiltration_mono ind).directed_le).mp hw
  obtain ⟨p₁, hp₁⟩ := hstage g
  obtain ⟨p₂, hp₂⟩ := hstage k
  exact hdesc (max p₁ p₂ - p₀ + 1).toNat (max p₁ p₂) (by omega) g k
    (rowFiniteIndexFiltration_mono ind (le_max_left _ _) hp₁)
    (rowFiniteIndexFiltration_mono ind (le_max_right _ _) hp₂) hg hgk

end Descent

/-- **Quasi-isomorphism invariance of twisted complexes.** Let `m` be a one-sided row-finite
twisting cocycle whose generator indices are bounded below. A quasi-isomorphism `f : M → N` of
DG right modules induces a quasi-isomorphism of the twisted complexes with coefficients in `M`
and in `N`. -/
theorem quasiIso_coefficientCochainComplexMap (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
    {p₀ : ℤ} (hp₀ : ∀ x, p₀ ≤ ind x) {f : DGRightModuleHom hM hN} (hf : f.IsQuasiIso) :
    QuasiIso (m.coefficientCochainComplexMap hM hN f) := by
  rw [quasiIso_coefficientCochainComplexMap_iff]
  intro n g k hg hk hdg hgk
  obtain ⟨u, v, hu, huv⟩ := m.exists_coefficientDifferential_eq_of_forall_exists hM hN hm f
    ((DGRightModuleHom.isQuasiIso_iff_forall_exists f).mp hf) hp₀ hdg hgk
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
