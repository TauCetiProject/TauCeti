/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Module.GradedModule.Internal
import TauCeti.Order.WellFounded.Basic

/-!
# Lifting maps out of semi-free row-finite twisted modules along quasi-isomorphisms

Let `m` be a row-finite twisting cocycle on a graded set of generators `(P, ind)` which is
**semi-free**: the relation `y ∈ (m.m x).support`, saying that `y` occurs in the row of `x`, is
well-founded. Its free differential graded left module `K_m = P →₀ A` is then built by attaching
the generators along this relation, each along a cycle in the span of the earlier ones. This holds
for instance when `m` is one-sided, `m x y = 0` whenever `ind x ≤ ind y`, with generator indices
bounded below (`TauCeti.RowFiniteTwistingCocycle.wellFounded_mem_support`). Maps out of `K_m` can
then be built one generator at a time. This file proves that such modules are **K-projective**
and **cofibrant**, and that lifts are unique up to homotopy:

* `TauCeti.RowFiniteTwistingCocycle.exists_lift_homotopy`: every degree-preserving chain map
  `g : K_m → N'` lifts, up to homotopy, along a quasi-isomorphism `φ : N → N'` of DG left
  modules. That is, there are a degree-preserving chain map `ĝ : K_m → N` and a homotopy `H` of
  degree `-1` with `g - φ ∘ ĝ = dN' ∘ H + H ∘ D`.
* `TauCeti.RowFiniteTwistingCocycle.exists_nullHomotopy`: every chain map from `K_m` to an
  acyclic DG left module is null-homotopic.
* `TauCeti.RowFiniteTwistingCocycle.exists_lift`: every chain map `K_m → N'` lifts strictly along
  a surjective quasi-isomorphism `N → N'`.
* `TauCeti.RowFiniteTwistingCocycle.exists_homotopy_of_homotopy_comp`: two chain maps
  `g₀ g₁ : K_m → N` with `φ ∘ g₀` homotopic to `φ ∘ g₁` are homotopic.

The quasi-isomorphism hypothesis is the elementwise statement that the mapping cone of `φ` is
acyclic: every relative cycle `(c, w)`, with `dN c = 0` and `φ c = dN' w`, is a relative
boundary `(dN u, φ u + dN' v)`. For right modules this is
`TauCeti.DGRightModuleHom.isQuasiIso_iff_forall_exists`.

A map out of the free module is given by the images of the generators, through
`Finsupp.linearCombination`, and a map of degree `-1` by the signed extension
`TauCeti.rowFiniteSignedMap` of the images of the generators, which carries the Koszul sign of
the coefficient. Both are determined by their values on generators: the chain map law and the
homotopy law hold on a vector as soon as they hold on the generators in its support
(`TauCeti.linearCombination_rowFiniteTwistedDifferential_of_forall_mem_support` and
`TauCeti.linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support`).

The lifts and homotopies choose the images of the generators by well-founded recursion along the
row relation (`WellFounded.exists_forall_of_forall_exists`). At a generator `x` the earlier
choices already make the image of its row `m x` into a relative cycle of `φ`, and a homogeneous
relative boundary bounding it gives the next choice
(`TauCeti.IsDGLeftModule.exists_mem_of_forall_exists`).

Applied to two semi-free resolutions `ε : K_{mP} → N` and `ε' : K_{mQ} → N` of the same module,
the lifting properties give continuation cocycles in both directions, with homotopies joining both
composites to the identity: the cocycles are homologous (`TauCeti.nonempty_rowFiniteHomologous`).
So for every DG right module `M` the twisted complexes `M ⊗_A K_{mP}` and `M ⊗_A K_{mQ}` are
homotopy equivalent (`TauCeti.RowFiniteHomologous.homotopyEquiv`), which is the independence of
the derived tensor product `M ⊗^L_A N` from the semi-free resolution used to compute it. In
particular a continuation cocycle which is a quasi-isomorphism is itself a homotopy equivalence
(`TauCeti.RowFiniteContinuationCocycle.exists_rowFiniteHomologous_ν_eq`).

## References

* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, GTM 205, Springer, 2001,
  Chapter 6 (semifree modules and the lifting lemma), Proposition 6.4.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uN uN' uP

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  {𝒩 : ℤ → Submodule R N} [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {dN : N →ₗ[R] N}
  {N' : Type uN'} [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {𝒩' : ℤ → Submodule R N'} [SetLike.GradedSMul 𝒜 𝒩'] [DirectSum.Decomposition 𝒩']
  {dN' : N' →ₗ[R] N'}

namespace RowFiniteTwistingCocycle

/-! ### Lifting along quasi-isomorphisms -/

section Lifting

variable {P : Type uP} {ind : P → ℤ} (m : RowFiniteTwistingCocycle 𝒜 d P ind)
  (hm : WellFounded fun y x ↦ y ∈ (m.m x).support)
  (hN : IsDGLeftModule hA 𝒩 dN) (hN' : IsDGLeftModule hA 𝒩' dN')
  {φ : N →ₗ[A] N'} (hφ : LinearMap.IsHomogeneous φ 𝒩 𝒩' 0)
  (hφd : ∀ y, φ (dN y) = dN' (φ y))
  (hrel : ∀ c w, dN c = 0 → φ c = dN' w → ∃ u v, dN u = c ∧ φ u + dN' v = w)
  {g : P → N'} (hg : ∀ x, g x ∈ 𝒩' (-ind x))
  (hgd : ∀ x, linearCombination A g (m.m x) = dN' (g x))

include hm hN hN' hφ hrel hg hgd in
/-- The lift up to homotopy of `exists_lift_homotopy`, with the chain map law and the homotopy
law stated on the generators. The images of the generators are chosen by well-founded recursion
along the row relation. -/
private theorem exists_lift_homotopy_generators :
    ∃ (ĝ : P → N) (k : P → N'), (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧ (∀ x, k x ∈ 𝒩' (-ind x - 1)) ∧
      (∀ x, linearCombination A ĝ (m.m x) = dN (ĝ x)) ∧
      ∀ x, g x - φ (ĝ x) = dN' (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x) := by
  classical
  -- An admissible pair of images at `x`, given the earlier images.
  let V : (P → N × N') → P → N × N' → Prop := fun F x v ↦
    v.1 ∈ 𝒩 (-ind x) ∧ v.2 ∈ 𝒩' (-ind x - 1) ∧
      linearCombination A (Prod.fst ∘ F) (m.m x) = dN v.1 ∧
      g x - φ v.1 = dN' v.2 + rowFiniteSignedMap (𝒜 := 𝒜) (Prod.snd ∘ F) (m.m x)
  suffices hGex : ∃ G : P → N × N', ∀ x, V G x (G x) by
    obtain ⟨G, hG⟩ := hGex
    exact ⟨Prod.fst ∘ G, Prod.snd ∘ G, fun x ↦ (hG x).1, fun x ↦ (hG x).2.1,
      fun x ↦ (hG x).2.2.1, fun x ↦ (hG x).2.2.2⟩
  refine hm.exists_forall_of_forall_exists V ?_ ?_
  · -- Admissibility only depends on the images of the generators in the row.
    rintro x v F F' hc ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨h₁, h₂, ?_, ?_⟩
    · rw [← h₃, linearCombination_apply, linearCombination_apply]
      exact Finsupp.sum_congr fun y hy ↦ by simp [hc y hy]
    · rw [h₄, rowFiniteSignedMap_congr (h' := Prod.snd ∘ F') fun y hy ↦ by simp [hc y hy]]
  · -- The image of the row is a relative cycle, and a bounding relative boundary is admissible.
    intro x F hval
    have hrow := m.m_mem_rowFiniteTotalGrading x
    have hc : linearCombination A (Prod.fst ∘ F) (m.m x) ∈ 𝒩 (1 - ind x) := by
      simpa using linearCombination_mem_of_forall_mem_support (j := 0) hrow fun y hy ↦ by
        simpa using (hval y hy).1
    have hw : g x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.snd ∘ F) (m.m x) ∈ 𝒩' (1 - ind x - 1) := by
      refine sub_mem (by simpa using hg x) ?_
      convert rowFiniteSignedMap_mem_of_forall_mem_support (h := Prod.snd ∘ F) (j := -1) hrow
        fun y hy ↦ by
          rw [Function.comp_apply]
          convert (hval y hy).2.1 using 2
          ring
      ring
    have hdc : dN (linearCombination A (Prod.fst ∘ F) (m.m x)) = 0 := by
      rw [← linearCombination_rowFiniteTwistedDifferential_of_forall_mem_support hN m.m
        fun y hy ↦ (hval y hy).2.2.1, m.differential_row x, map_zero]
    have hcw : φ (linearCombination A (Prod.fst ∘ F) (m.m x)) =
        dN' (g x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.snd ∘ F) (m.m x)) := by
      have key := linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support hN' m.m
        (e := fun y ↦ g y - φ (F y).1) (k := Prod.snd ∘ F) fun y hy ↦ (hval y hy).2.2.2
      rw [m.differential_row x, map_zero, add_zero] at key
      simp only [linearCombination_apply, smul_sub, sum_sub] at key
      rw [map_sub, ← key, ← hgd x, linearCombination_apply, linearCombination_apply,
        map_finsuppSum]
      simp
    obtain ⟨u, v, hu, hv, hdu, huv⟩ := hN.exists_mem_of_forall_exists hN' hφ hrel hc hw hdc hcw
    refine ⟨(u, v), by simpa using hu, by simpa [sub_sub] using hv, hdu.symm, ?_⟩
    rw [eq_sub_iff_add_eq] at huv
    rw [← huv]
    abel

include hm hN hN' hφ hrel hg hgd in
/-- **Semi-free modules are K-projective: lifting along quasi-isomorphisms up to homotopy.**
Let `m` be semi-free, the relation `y ∈ (m.m x).support` being well-founded, and let
`φ : N → N'` be a degree-preserving `A`-linear map whose relative cycles are relative boundaries:
every `(c, w)` with `dN c = 0` and `φ c = dN' w` is `(dN u, φ u + dN' v)`. For a morphism of DG
left modules this says that `φ` is a quasi-isomorphism. Then every degree-preserving chain map
`g : K_m → N'`, given by the images of the generators, lifts up to homotopy along `φ`: there are
a degree-preserving chain map `ĝ : K_m → N` and a homotopy `H` of degree `-1`, the signed
extension of `k`, with `g - φ ∘ ĝ = dN' ∘ H + H ∘ D`. -/
theorem exists_lift_homotopy :
    ∃ (ĝ : P → N) (k : P → N'), (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧ (∀ x, k x ∈ 𝒩' (-ind x - 1)) ∧
      (∀ f, linearCombination A ĝ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
        dN (linearCombination A ĝ f)) ∧
      ∀ f, linearCombination A g f - φ (linearCombination A ĝ f) =
        dN' (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
          rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) := by
  obtain ⟨ĝ, k, hĝ, hk, hĝd, hgk⟩ := exists_lift_homotopy_generators m hm hN hN' hφ hrel hg hgd
  refine ⟨ĝ, k, hĝ, hk, linearCombination_rowFiniteTwistedDifferential hN m.m hĝd, fun f ↦ ?_⟩
  rw [← linearCombination_eq_add_rowFiniteSignedMap hN' m.m (e := fun y ↦ g y - φ (ĝ y)) hgk f]
  simp [linearCombination_apply, smul_sub, sum_sub, map_finsuppSum]

include hm hN in
/-- **Semi-free modules are K-projective: maps into acyclic modules are null-homotopic.** Let
`m` be semi-free, and let `N` be an acyclic DG left module: every cycle is a boundary. Then every
degree-preserving chain map `g : K_m → N` is null-homotopic: `g = dN ∘ H + H ∘ D` for the signed
extension `H` of some `k` of degree `-1`. -/
theorem exists_nullHomotopy (hacyc : ∀ c, dN c = 0 → ∃ u, dN u = c) {g : P → N}
    (hg : ∀ x, g x ∈ 𝒩 (-ind x)) (hgd : ∀ x, linearCombination A g (m.m x) = dN (g x)) :
    ∃ k : P → N, (∀ x, k x ∈ 𝒩 (-ind x - 1)) ∧
      ∀ f, linearCombination A g f = dN (rowFiniteSignedMap (𝒜 := 𝒜) k f) +
        rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) := by
  obtain ⟨_, k, _, hk, _, hgk⟩ := exists_lift_homotopy m hm hN hN
    (LinearMap.isHomogeneous_zero 𝒩 𝒩 0) (φ := 0)
    (fun c w hc hw ↦ by
      obtain ⟨u, hu⟩ := hacyc c hc
      obtain ⟨v, hv⟩ := hacyc w (by simpa using hw.symm)
      exact ⟨u, v, hu, by simpa using hv⟩) hg hgd
  exact ⟨k, hk, fun f ↦ by simpa using hgk f⟩

include hm hN hN' hφ hφd hrel hg hgd in
/-- **Semi-free modules are cofibrant: strict lifting along surjective quasi-isomorphisms.** Let
`m` be semi-free, and let `φ : N → N'` be a surjective degree-preserving quasi-isomorphism of DG
left modules. Then every degree-preserving chain map `g : K_m → N'` factors through `φ` as a
degree-preserving chain map `ĝ : K_m → N`. -/
theorem exists_lift (hφs : Function.Surjective φ) :
    ∃ ĝ : P → N, (∀ x, ĝ x ∈ 𝒩 (-ind x)) ∧
      (∀ f, linearCombination A ĝ (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) =
        dN (linearCombination A ĝ f)) ∧
      ∀ f, φ (linearCombination A ĝ f) = linearCombination A g f := by
  classical
  obtain ⟨ĝ, k, hĝ, hk, hĝd, hgk⟩ := exists_lift_homotopy m hm hN hN' hφ hrel hg hgd
  -- Lift the homotopy to `N`, in the same degrees.
  have hlift (x : P) : ∃ l : N, l ∈ 𝒩 (-ind x - 1) ∧ φ l = k x := by
    obtain ⟨l, hl⟩ := hφs (k x)
    refine ⟨DirectSum.decompose 𝒩 l (-ind x - 1), SetLike.coe_mem _, ?_⟩
    rw [hφ.map_decompose, add_zero, hl, DirectSum.decompose_of_mem_same _ (hk x)]
  choose l hl hφl using hlift
  have hφk : φ ∘ l = k := funext hφl
  -- Correct the lift by the null-homotopic map `dN ∘ L + L ∘ D`, where `L` lifts the homotopy.
  let e (x : P) : N := dN (l x) + rowFiniteSignedMap (𝒜 := 𝒜) l (m.m x)
  have he (f : P →₀ A) : linearCombination A e f = dN (rowFiniteSignedMap (𝒜 := 𝒜) l f) +
      rowFiniteSignedMap (𝒜 := 𝒜) l (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) m.m f) :=
    linearCombination_eq_add_rowFiniteSignedMap hN m.m (fun _ ↦ rfl) f
  have hsum (f : P →₀ A) :
      linearCombination A (ĝ + e) f = linearCombination A ĝ f + linearCombination A e f := by
    simp [linearCombination_apply, smul_add, sum_add]
  have hφS (f : P →₀ A) :
      φ (rowFiniteSignedMap (𝒜 := 𝒜) l f) = rowFiniteSignedMap (𝒜 := 𝒜) k f := by
    rw [LinearMap.map_rowFiniteSignedMap, hφk]
  refine ⟨ĝ + e, fun x ↦ add_mem (hĝ x) (add_mem ?_ ?_), fun f ↦ ?_, fun f ↦ ?_⟩
  · convert hN.isHomogeneous.map_mem (hl x) using 2
    ring
  · convert rowFiniteSignedMap_mem_of_mem_rowFiniteTotalGrading (j := -1)
      (fun y ↦ by convert hl y using 2; ring) (m.m_mem_rowFiniteTotalGrading x) using 2
    ring
  · rw [hsum, hsum, hĝd, he, he, m.differential_sq_zero hA, map_zero, add_zero]
    simp only [map_add, hN.sq_zero, zero_add]
  · rw [hsum, map_add, he, map_add, hφd, hφS, hφS, ← hgk f]
    abel

include hm hN hN' hφ hrel in
/-- **Uniqueness of lifts up to homotopy.** Let `m` be semi-free, the relation
`y ∈ (m.m x).support` being well-founded, and let `φ : N → N'` be a degree-preserving `A`-linear
map whose relative cycles are relative boundaries. If two chain maps `g₀ g₁ : K_m → N` become
homotopic after composing with `φ`, through a homotopy `k` with
`dN' (k x) + k (m x) = φ (g₁ x) - φ (g₀ x)`, then they are homotopic. -/
theorem exists_homotopy_of_homotopy_comp {g₀ g₁ : P → N} (hg₀ : ∀ x, g₀ x ∈ 𝒩 (-ind x))
    (hg₁ : ∀ x, g₁ x ∈ 𝒩 (-ind x))
    (hg₀d : ∀ x, linearCombination A g₀ (m.m x) = dN (g₀ x))
    (hg₁d : ∀ x, linearCombination A g₁ (m.m x) = dN (g₁ x))
    {k : P → N'} (hk : ∀ x, k x ∈ 𝒩' (-ind x - 1))
    (hkd : ∀ x, dN' (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (m.m x) = φ (g₁ x) - φ (g₀ x)) :
    ∃ h : P → N, (∀ x, h x ∈ 𝒩 (-ind x - 1)) ∧
      ∀ x, dN (h x) + rowFiniteSignedMap (𝒜 := 𝒜) h (m.m x) = g₁ x - g₀ x := by
  classical
  -- An admissible pair at `x`: the homotopy `h x`, together with a second-order homotopy `l x`
  -- from `k` to `φ ∘ h`, given the earlier choices.
  let V : (P → N × N') → P → N × N' → Prop := fun F x v ↦
    v.1 ∈ 𝒩 (-ind x - 1) ∧ v.2 ∈ 𝒩' (-ind x - 1 - 1) ∧
      dN v.1 + rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x) = g₁ x - g₀ x ∧
      k x - φ v.1 = dN' v.2 - linearCombination A (Prod.snd ∘ F) (m.m x)
  suffices hGex : ∃ G : P → N × N', ∀ x, V G x (G x) by
    obtain ⟨G, hG⟩ := hGex
    exact ⟨Prod.fst ∘ G, fun x ↦ (hG x).1, fun x ↦ (hG x).2.2.1⟩
  refine hm.exists_forall_of_forall_exists V ?_ ?_
  · -- Admissibility only depends on the choices at the generators in the row.
    rintro x v F F' hc ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨h₁, h₂, ?_, ?_⟩
    · rw [← h₃, rowFiniteSignedMap_congr (h' := Prod.fst ∘ F) fun y hy ↦ by simp [hc y hy]]
    · rw [h₄, linearCombination_apply, linearCombination_apply]
      congr 1
      exact Finsupp.sum_congr fun y hy ↦ by simp [hc y hy]
  · intro x F hval
    have hrow := m.m_mem_rowFiniteTotalGrading x
    -- The relative cycle `(c, w)` of `φ` at `x`.
    have hc : g₁ x - g₀ x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x) ∈ 𝒩 (-ind x) := by
      refine sub_mem (sub_mem (hg₁ x) (hg₀ x)) ?_
      convert rowFiniteSignedMap_mem_of_forall_mem_support (h := Prod.fst ∘ F) (j := -1) hrow
        fun y hy ↦ by
          rw [Function.comp_apply]
          convert (hval y hy).1 using 2
          ring
      ring
    have hw : k x + linearCombination A (Prod.snd ∘ F) (m.m x) ∈ 𝒩' (-ind x - 1) := by
      refine add_mem (hk x) ?_
      convert linearCombination_mem_of_forall_mem_support (g := Prod.snd ∘ F) (j := -1 - 1) hrow
        fun y hy ↦ by
          rw [Function.comp_apply]
          convert (hval y hy).2.1 using 2
          ring
      ring
    -- The homotopy relation on the row of `x`, from the earlier choices.
    have hH := linearCombination_eq_add_rowFiniteSignedMap_of_forall_mem_support hN m.m
      (e := fun y ↦ g₁ y - g₀ y) (k := Prod.fst ∘ F) (f := m.m x)
      fun y hy ↦ ((hval y hy).2.2.1).symm
    rw [m.differential_row x, map_zero, add_zero] at hH
    -- The second-order relation on the row of `x`, from the earlier choices.
    have hL := rowFiniteSignedMap_eq_of_forall_mem_support hN' m.m
      (θ := k - φ ∘ (Prod.fst ∘ F)) (l := Prod.snd ∘ F) (f := m.m x) fun y hy ↦ by
        simpa using (hval y hy).2.2.2
    rw [m.differential_row x, map_zero, sub_zero, rowFiniteSignedMap_sub, LinearMap.sub_apply,
      ← LinearMap.map_rowFiniteSignedMap] at hL
    have hdc : dN (g₁ x - g₀ x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x)) = 0 := by
      rw [map_sub, map_sub, ← hH, ← hg₀d, ← hg₁d]
      simp [linearCombination_apply, smul_sub, sum_sub]
    have hcw : φ (g₁ x - g₀ x - rowFiniteSignedMap (𝒜 := 𝒜) (Prod.fst ∘ F) (m.m x)) =
        dN' (k x + linearCombination A (Prod.snd ∘ F) (m.m x)) := by
      rw [map_add, ← hL, map_sub, map_sub, ← hkd x]
      abel
    obtain ⟨u, v, hu, hv, hdu, huv⟩ := hN.exists_mem_of_forall_exists hN' hφ hrel
      (n := -ind x) hc (by simpa using hw) hdc hcw
    refine ⟨(u, v), hu, hv, ?_, ?_⟩
    · simp only
      rw [hdu]
      abel
    · calc k x - φ u
          = k x + linearCombination A (Prod.snd ∘ F) (m.m x) - φ u -
              linearCombination A (Prod.snd ∘ F) (m.m x) := by abel
        _ = φ u + dN' v - φ u - linearCombination A (Prod.snd ∘ F) (m.m x) := by rw [huv]
        _ = dN' v - linearCombination A (Prod.snd ∘ F) (m.m x) := by abel

end Lifting

end RowFiniteTwistingCocycle

/-! ### Semi-free resolutions are unique up to homotopy -/

section Homologous

variable {P Q : Type uP} {indP : P → ℤ} {indQ : Q → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}

/-- The lift up to homotopy of a chain map `ε : K_{mP} → N` along a chain map `ε' : K_{mQ} → N`
whose relative cycles are relative boundaries, as a continuation cocycle `ν` from `mP` to `mQ`
and a homotopy `k` from `ε' ∘ ν` to `ε` given on the generators. -/
private theorem exists_rowFiniteContinuationCocycle_homotopy
    (hmP : WellFounded fun y x ↦ y ∈ (mP.m x).support)
    (hN : IsDGLeftModule hA 𝒩 dN) {ε : P → N} {ε' : Q → N}
    (hε : ∀ x, ε x ∈ 𝒩 (-indP x)) (hε' : ∀ y, ε' y ∈ 𝒩 (-indQ y))
    (hεd : ∀ x, linearCombination A ε (mP.m x) = dN (ε x))
    (hε'rel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m c = 0 →
      linearCombination A ε' c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m u = c ∧
          linearCombination A ε' u + dN v = w) :
    ∃ (ν : RowFiniteContinuationCocycle mP mQ) (k : P → N), (∀ x, k x ∈ 𝒩 (-indP x - 1)) ∧
      ∀ x, dN (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (mP.m x) =
        ε x - linearCombination A ε' (ν.ν x) := by
  obtain ⟨ν, k, hν, hk, hνd, hkd⟩ := mP.exists_lift_homotopy_generators hmP
    (mQ.isDGLeftModule_rowFiniteTwistedDifferential hA) hN
    (isHomogeneous_linearCombination hε') hε'rel hε hεd
  exact ⟨.ofTotalGrading ν hν hνd, k, hk, fun x ↦ by
    rw [RowFiniteContinuationCocycle.ofTotalGrading_ν]
    exact (hkd x).symm⟩

/-- Two lifts between semi-free resolutions `ε` and `ε'`, in opposite directions, compose to a
continuation cocycle homotopic to the identity of the target of the second. -/
private theorem nonempty_rowFiniteParametrizedCocycle_refl_comp
    (hmQ : WellFounded fun y x ↦ y ∈ (mQ.m x).support)
    (hN : IsDGLeftModule hA 𝒩 dN) {ε : P → N} {ε' : Q → N} (hε' : ∀ y, ε' y ∈ 𝒩 (-indQ y))
    (hε'rel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m c = 0 →
      linearCombination A ε' c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m u = c ∧
          linearCombination A ε' u + dN v = w)
    (ν : RowFiniteContinuationCocycle mP mQ) (ν' : RowFiniteContinuationCocycle mQ mP)
    {k : P → N} (hk : ∀ x, k x ∈ 𝒩 (-indP x - 1))
    (hkd : ∀ x, dN (k x) + rowFiniteSignedMap (𝒜 := 𝒜) k (mP.m x) =
      ε x - linearCombination A ε' (ν.ν x))
    {k' : Q → N} (hk' : ∀ y, k' y ∈ 𝒩 (-indQ y - 1))
    (hk'd : ∀ y, dN (k' y) + rowFiniteSignedMap (𝒜 := 𝒜) k' (mQ.m y) =
      ε' y - linearCombination A ε (ν'.ν y)) :
    Nonempty (RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mQ hA)
      (ν'.comp ν hA)) := by
  have hNQ := mQ.isDGLeftModule_rowFiniteTwistedDifferential hA
  -- The homotopy `k` on generators extends to the whole free module.
  have hkv (w : P →₀ A) : linearCombination A ε w - linearCombination A ε'
      (linearCombination A ν.ν w) = dN (rowFiniteSignedMap (𝒜 := 𝒜) k w) +
        rowFiniteSignedMap (𝒜 := 𝒜) k (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m w) := by
    rw [← linearCombination_eq_add_rowFiniteSignedMap hN mP.m
      (e := fun x ↦ ε x - linearCombination A ε' (ν.ν x)) (fun x ↦ (hkd x).symm) w]
    simp [linearCombination_apply, smul_sub, sum_sub, map_finsuppSum]
  obtain ⟨h, hh, hhd⟩ := mQ.exists_homotopy_of_homotopy_comp hmQ hNQ hN
    (isHomogeneous_linearCombination hε') hε'rel
    (g₀ := (RowFiniteContinuationCocycle.refl mQ hA).ν) (g₁ := (ν'.comp ν hA).ν)
    (fun y ↦ (RowFiniteContinuationCocycle.refl mQ hA).ν_mem_rowFiniteTotalGrading y)
    (fun y ↦ (ν'.comp ν hA).ν_mem_rowFiniteTotalGrading y)
    (fun y ↦ ((RowFiniteContinuationCocycle.refl mQ hA).continuation y).symm)
    (fun y ↦ ((ν'.comp ν hA).continuation y).symm)
    (k := -(k' + fun y ↦ rowFiniteSignedMap (𝒜 := 𝒜) k (ν'.ν y)))
    (fun y ↦ neg_mem (add_mem (hk' y) (by
      convert rowFiniteSignedMap_mem_of_forall_mem_support (j := -1)
        (ν'.ν_mem_rowFiniteTotalGrading y) fun x _ ↦ by
          convert hk x using 2
          ring
      ring)))
    (fun y ↦ by
      have hv := hkv (ν'.ν y)
      rw [ν'.continuation y] at hv
      have h₁ : linearCombination A ε' (linearCombination A ν.ν (ν'.ν y)) =
          linearCombination A ε (ν'.ν y) -
            (dN (rowFiniteSignedMap (𝒜 := 𝒜) k (ν'.ν y)) +
              rowFiniteSignedMap (𝒜 := 𝒜) k (linearCombination A ν'.ν (mQ.m y))) := by
        rw [← hv]
        abel
      have h₂ : linearCombination A ε (ν'.ν y) =
          ε' y - (dN (k' y) + rowFiniteSignedMap (𝒜 := 𝒜) k' (mQ.m y)) := by
        rw [hk'd y]
        abel
      rw [rowFiniteSignedMap_neg, rowFiniteSignedMap_add, LinearMap.neg_apply, LinearMap.add_apply,
        rowFiniteSignedMap_linearCombination,
        RowFiniteContinuationCocycle.comp_ν, RowFiniteContinuationCocycle.refl_ν,
        linearCombination_single, one_smul, h₁, h₂]
      simp only [Pi.neg_apply, Pi.add_apply, map_neg, map_add]
      abel)
  exact ⟨.ofTotalGrading h hh hhd⟩

/-- **Semi-free resolutions are unique up to homotopy.** Let `ε : K_{mP} → N` and
`ε' : K_{mQ} → N` be chain maps from two semi-free row-finite twisted modules, with well-founded
row relations, to the same DG left module, whose relative cycles are relative
boundaries. Then `mP` and `mQ` are homologous, so their twisted complexes with coefficients in
any DG right module are homotopy equivalent (`TauCeti.RowFiniteHomologous.homotopyEquiv`). -/
theorem nonempty_rowFiniteHomologous
    (hmP : WellFounded fun y x ↦ y ∈ (mP.m x).support)
    (hmQ : WellFounded fun y x ↦ y ∈ (mQ.m x).support)
    (hN : IsDGLeftModule hA 𝒩 dN) {ε : P → N} {ε' : Q → N}
    (hε : ∀ x, ε x ∈ 𝒩 (-indP x)) (hε' : ∀ y, ε' y ∈ 𝒩 (-indQ y))
    (hεd : ∀ x, linearCombination A ε (mP.m x) = dN (ε x))
    (hε'd : ∀ y, linearCombination A ε' (mQ.m y) = dN (ε' y))
    (hεrel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      linearCombination A ε c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
          linearCombination A ε u + dN v = w)
    (hε'rel : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m c = 0 →
      linearCombination A ε' c = dN w →
        ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m u = c ∧
          linearCombination A ε' u + dN v = w) :
    Nonempty (RowFiniteHomologous hA mP mQ) := by
  obtain ⟨c, k, hk, hkd⟩ :=
    exists_rowFiniteContinuationCocycle_homotopy hmP hN hε hε' hεd hε'rel
  obtain ⟨c', k', hk', hk'd⟩ :=
    exists_rowFiniteContinuationCocycle_homotopy hmQ hN hε' hε hε'd hεrel
  obtain ⟨homQ⟩ := nonempty_rowFiniteParametrizedCocycle_refl_comp hmQ hN hε' hε'rel c c'
    hk hkd hk' hk'd
  obtain ⟨homP⟩ := nonempty_rowFiniteParametrizedCocycle_refl_comp hmP hN hε hεrel c' c
    hk' hk'd hk hkd
  exact ⟨⟨c, c', homP, homQ⟩⟩

/-- **A quasi-isomorphism of semi-free twisted modules is a homotopy equivalence.** Let `mP` and
`mQ` be semi-free, with well-founded row relations, and let `ν` be a continuation cocycle
from `mP` to `mQ` whose relative cycles are relative boundaries. Then `ν` is part of a
homotopy equivalence: there is a continuation cocycle back with both composites homotopic to the
identity. -/
theorem RowFiniteContinuationCocycle.exists_rowFiniteHomologous_ν_eq
    (hmP : WellFounded fun y x ↦ y ∈ (mP.m x).support)
    (hmQ : WellFounded fun y x ↦ y ∈ (mQ.m x).support)
    (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ c w, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m c = 0 →
      linearCombination A ν.ν c = rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m w →
      ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mP.m u = c ∧
        linearCombination A ν.ν u + rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) mQ.m v = w) :
    ∃ H : RowFiniteHomologous hA mP mQ, H.ν = ν := by
  have hNQ := mQ.isDGLeftModule_rowFiniteTwistedDifferential hA
  -- Lift the identity of `K_{mQ}` along `ν`.
  obtain ⟨c', k', hk', hk'd⟩ := exists_rowFiniteContinuationCocycle_homotopy hmQ hNQ
    (RowFiniteContinuationCocycle.refl mQ hA).ν_mem_rowFiniteTotalGrading
    ν.ν_mem_rowFiniteTotalGrading
    (fun y ↦ ((RowFiniteContinuationCocycle.refl mQ hA).continuation y).symm) hν
  have homQ :
      RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mQ hA) (c'.comp ν hA) :=
    .ofTotalGrading (-k') (fun y ↦ neg_mem (hk' y)) fun y ↦ by
      rw [Pi.neg_apply, map_neg, rowFiniteSignedMap_neg, LinearMap.neg_apply, ← neg_add, hk'd y,
        neg_sub, RowFiniteContinuationCocycle.comp_ν]
  have hrefl : ∀ x, linearCombination A (RowFiniteContinuationCocycle.refl mQ hA).ν
      (ν.ν x) = ν.ν x := fun x ↦ by
    have := congrArg (fun μ : RowFiniteContinuationCocycle mP mQ ↦ μ.ν x) (ν.comp_refl hA)
    simpa only [RowFiniteContinuationCocycle.comp_ν] using this
  obtain ⟨homP⟩ := nonempty_rowFiniteParametrizedCocycle_refl_comp hmP hNQ
    (ε := (RowFiniteContinuationCocycle.refl mQ hA).ν) (ε' := ν.ν) ν.ν_mem_rowFiniteTotalGrading
    hν c' ν
    (k := k') hk' hk'd (k' := 0) (fun _ ↦ zero_mem _)
    (fun x ↦ by simp [hrefl, rowFiniteSignedMap_apply])
  exact ⟨⟨ν, c', homP, homQ⟩, rfl⟩

end Homologous

end TauCeti
