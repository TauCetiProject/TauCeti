/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Tower
public import TauCeti.LinearAlgebra.Finsupp.Supported

/-!
# Semi-free resolutions of differential graded left modules

Every differential graded left module `N` over a differential graded algebra `A` has a
**semi-free resolution**: a row-finite twisted module `K_m = P →₀ A` whose row relation is
well-founded, with a surjective chain map `ε : K_m → N` that is a quasi-isomorphism. This file
constructs one, `TauCeti.semifreeResolution`, by attaching free generators along cycles.

Start with no generators. At each stage, with free module `K` and chain map `ε : K → N`,
attach one free generator `e` for every homogeneous **relative cycle** `(c, w)` of `ε`: a cycle
`c` of `K` of total degree `n + 1` and an element `w ∈ N` of degree `n` with `ε c = dN w`. The
generator `e` has degree `n` and differential `c`, and is sent to `w`; this is a chain map
because `ε c = dN w`. The resolution is the union of the stages. Its generators are the pairs
`(k, (c, w))` of a stage `k` and a relative cycle of that stage; the row of a generator only
involves generators of earlier stages, so the row relation is well-founded. The stages and their
union are the tower of cell attachments `TauCeti.RowFiniteAugmentedModule.tower`, whose step
attaches all the homogeneous relative cycles of the current stage.

The construction has a single characteristic property
(`TauCeti.exists_semifreeResolution_m_eq`): every homogeneous relative cycle `(c, w)` of the
union is the row and the image of a generator, since `c` already lives in some stage. Everything
else follows:

* the relative cycles of `ε` are relative boundaries, so `ε` is a quasi-isomorphism
  (`TauCeti.exists_rowFiniteTwistedDifferential_semifreeResolution_eq`);
* `ε` is onto (`TauCeti.linearCombination_semifreeResolutionAugmentation_surjective`): a
  homogeneous `y` is the image of a generator attached along the generator sent to `dN y`.

The lifting theorems of `TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Lifting` apply to this
resolution: it is K-projective, and it is homologous to every other semi-free resolution of `N`
whose generators live in the same universe (`TauCeti.exists_rowFiniteHomologous_homotopy`). So
for a DG right module `M`, the twisted complex `M ⊗_A K_m`
(`TauCeti.RowFiniteTwistingCocycle.coefficientCochainComplex`), the model of the derived tensor
product `M ⊗^L_A N`, exists for every `N` and does not depend, up to homotopy equivalence, on the
semi-free resolution used.

## Main definitions

* `TauCeti.semifreeResolutionGenerator`: the generators, with their indices
  `TauCeti.semifreeResolutionIndex`.
* `TauCeti.semifreeResolution`: the twisting cocycle of the resolution.
* `TauCeti.semifreeResolutionAugmentation`: the images of the generators in `N`.

## Main results

* `TauCeti.wellFounded_mem_support_semifreeResolution`: the resolution is semi-free.
* `TauCeti.linearCombination_semifreeResolutionAugmentation_m`: the augmentation is a chain map.
* `TauCeti.exists_semifreeResolution_m_eq`: every homogeneous relative cycle of the augmentation
  is the row and the image of a generator.
* `TauCeti.exists_rowFiniteTwistedDifferential_semifreeResolution_eq`: the relative cycles of the
  augmentation are relative boundaries.
* `TauCeti.linearCombination_semifreeResolutionAugmentation_surjective`: the augmentation is
  onto.

## References

* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6, Proposition 6.6.
* B. Keller, *Deriving DG categories*, Ann. Sci. École Norm. Sup. (4) 27 (1994), Section 3.
-/

public noncomputable section

open Finsupp

namespace TauCeti

universe uR uA uN

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜] (d : A →ₗ[R] A)
  {N : Type uN} [AddCommGroup N] [Module R N] [Module A N]
  (𝒩 : ℤ → Submodule R N) (dN : N →ₗ[R] N)

/-! ### The stages of the construction -/

/-- A homogeneous relative cycle `(c, w)` of the chain map of a stage: a cycle `c` of total degree
`n + 1` and an element `w` of degree `n` with `ε c = dN w`. -/
private structure ResolutionCycle
    (S : RowFiniteAugmentedModule.{uR, uA, uN, max uA uN} 𝒜 d 𝒩 dN) where
  /-- The degree of `w`. -/
  n : ℤ
  /-- The cycle of the free module. -/
  c : S.P →₀ A
  /-- The element of `N` bounding the image of `c`. -/
  w : N
  /-- `c` has total degree `n + 1`. -/
  c_mem : c ∈ rowFiniteTotalGrading 𝒜 S.ind (n + 1)
  /-- `w` has degree `n`. -/
  w_mem : w ∈ 𝒩 n
  /-- `c` is a cycle. -/
  c_cycle : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) S.m.m c = 0
  /-- `w` bounds the image of `c`. -/
  ε_c : linearCombination A S.g c = dN w

/-- The step of the construction: one free generator is attached along every homogeneous relative
cycle, with differential its cycle and image its element of `N`. -/
private def resolutionStep (_ : ℕ) (S : RowFiniteAugmentedModule.{uR, uA, uN, max uA uN} 𝒜 d 𝒩 dN) :
    S.Attachment fun t : ResolutionCycle 𝒜 d 𝒩 dN S ↦ -t.n where
  a t := t.c
  ha t y := by
    convert (mem_rowFiniteTotalGrading_iff 𝒜 S.ind).mp t.c_mem y using 2
    ring
  hca t := t.c_cycle
  c t := t.w
  c_mem t := by simpa using t.w_mem
  g_a t := t.ε_c

/-- The stages of the construction, each obtained from the previous one by attaching generators
along all of its homogeneous relative cycles. -/
private abbrev resolutionStage (k : ℕ) :
    RowFiniteAugmentedModule.{uR, uA, uN, max uA uN} 𝒜 d 𝒩 dN :=
  RowFiniteAugmentedModule.tower (resolutionStep 𝒜 d 𝒩 dN) k

/-! ### The resolution -/

/-- The generators of the semi-free resolution: a generator is a stage `k` together with a
homogeneous relative cycle of the chain map of that stage, along which it is attached. -/
def semifreeResolutionGenerator : Type (max uA uN) :=
  Σ k, ResolutionCycle 𝒜 d 𝒩 dN (resolutionStage 𝒜 d 𝒩 dN k)

/-- The index of a generator of the semi-free resolution: the generator attached along a relative
cycle `(c, w)` with `w` of degree `n` has index `-n`, so that it lies in degree `n`. -/
def semifreeResolutionIndex (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) : ℤ :=
  -x.2.n

/-- **The semi-free resolution** of `N`: the twisting cocycle on the generators of all stages, in
which the generator attached along a relative cycle `(c, w)` has row `c`. -/
def semifreeResolution :
    RowFiniteTwistingCocycle 𝒜 d (semifreeResolutionGenerator 𝒜 d 𝒩 dN)
      (semifreeResolutionIndex 𝒜 d 𝒩 dN) :=
  RowFiniteAugmentedModule.towerCocycle (resolutionStep 𝒜 d 𝒩 dN)

/-- The augmentation of the semi-free resolution: the generator attached along a relative cycle
`(c, w)` is sent to `w`. -/
def semifreeResolutionAugmentation : semifreeResolutionGenerator 𝒜 d 𝒩 dN → N :=
  RowFiniteAugmentedModule.towerAugmentation (resolutionStep 𝒜 d 𝒩 dN)

variable {𝒜 d 𝒩 dN}

/-! ### The characteristic property and its consequences -/

/-- **The resolution is semi-free**: the row of a generator only involves generators attached at
earlier stages, so the relation `y ∈ (m x).support` is well-founded. -/
theorem wellFounded_mem_support_semifreeResolution :
    WellFounded fun y x ↦ y ∈ ((semifreeResolution 𝒜 d 𝒩 dN).m x).support :=
  RowFiniteAugmentedModule.wellFounded_mem_support_towerCocycle (resolutionStep 𝒜 d 𝒩 dN)

/-- The augmentation preserves degrees: a generator of index `i` is sent to degree `-i`. -/
theorem semifreeResolutionAugmentation_mem (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    semifreeResolutionAugmentation 𝒜 d 𝒩 dN x ∈ 𝒩 (-semifreeResolutionIndex 𝒜 d 𝒩 dN x) :=
  RowFiniteAugmentedModule.towerAugmentation_mem (resolutionStep 𝒜 d 𝒩 dN) x

/-- **The augmentation is a chain map**, on the generators: the image of the row of a generator
is the differential of its image. -/
theorem linearCombination_semifreeResolutionAugmentation_m
    (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN)
      ((semifreeResolution 𝒜 d 𝒩 dN).m x) = dN (semifreeResolutionAugmentation 𝒜 d 𝒩 dN x) :=
  RowFiniteAugmentedModule.linearCombination_towerAugmentation_m (resolutionStep 𝒜 d 𝒩 dN) x

/-- **The characteristic property of the resolution**: every homogeneous relative cycle of the
augmentation, a cycle `c` of total degree `n + 1` and an element `w` of degree `n` with
`ε c = dN w`, is the row and the image of a generator, of index `-n`. -/
theorem exists_semifreeResolution_m_eq {n : ℤ} {c : semifreeResolutionGenerator 𝒜 d 𝒩 dN →₀ A}
    {w : N} (hc : c ∈ rowFiniteTotalGrading 𝒜 (semifreeResolutionIndex 𝒜 d 𝒩 dN) (n + 1))
    (hw : w ∈ 𝒩 n)
    (hdc : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (semifreeResolution 𝒜 d 𝒩 dN).m c = 0)
    (hcw : linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN) c = dN w) :
    ∃ x, semifreeResolutionIndex 𝒜 d 𝒩 dN x = -n ∧ (semifreeResolution 𝒜 d 𝒩 dN).m x = c ∧
      semifreeResolutionAugmentation 𝒜 d 𝒩 dN x = w := by
  classical
  -- `semifreeResolution` is by definition the union `towerCocycle` of the tower of stages.
  -- `c` involves finitely many generators, so it comes from some stage `k`.
  obtain ⟨k, hk⟩ := exists_mem_supported_lt (R := A) Sigma.fst c
  obtain ⟨c', rfl⟩ :=
    RowFiniteAugmentedModule.exists_mapDomain_towerOf_eq (resolutionStep 𝒜 d 𝒩 dN) hk
  refine ⟨⟨k, ⟨n, c', w, ?_, hw, ?_, ?_⟩⟩, rfl,
    RowFiniteAugmentedModule.towerCocycle_m (resolutionStep 𝒜 d 𝒩 dN) _,
    RowFiniteAugmentedModule.towerAugmentation_mk (resolutionStep 𝒜 d 𝒩 dN) _ _⟩
  · exact (mapDomain_mem_rowFiniteTotalGrading_iff 𝒜 _
      (RowFiniteAugmentedModule.towerOf_injective _ k)
      (RowFiniteAugmentedModule.indQ_towerOf _ k)).mp hc
  · exact (RowFiniteAugmentedModule.rowFiniteTwistedDifferential_towerCocycle_mapDomain_eq_zero_iff
      _ k c').mp hdc
  · rw [← RowFiniteAugmentedModule.linearCombination_towerAugmentation_mapDomain]
    exact hcw

variable [IsScalarTower R A N] [SetLike.GradedSMul 𝒜 𝒩] [DirectSum.Decomposition 𝒩]
  {hA : IsDGAlgebra 𝒜 d}

/-- **The augmentation is a quasi-isomorphism**: every relative cycle `(c, w)`, with `D c = 0`
and `ε c = dN w`, is a relative boundary `(D u, ε u + dN v)`. For a homogeneous relative cycle,
`u` is the generator attached along it and `v = 0`. -/
theorem exists_rowFiniteTwistedDifferential_semifreeResolution_eq (hN : IsDGLeftModule hA 𝒩 dN)
    (c : semifreeResolutionGenerator 𝒜 d 𝒩 dN →₀ A) (w : N)
    (hc : rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (semifreeResolution 𝒜 d 𝒩 dN).m c = 0)
    (hcw : linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN) c = dN w) :
    ∃ u v, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (semifreeResolution 𝒜 d 𝒩 dN).m u = c ∧
      linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN) u + dN v = w := by
  refine ((semifreeResolution 𝒜 d 𝒩 dN).isDGLeftModule_rowFiniteTwistedDifferential hA)
    |>.exists_of_forall_mem_exists hN
      (isHomogeneous_linearCombination semifreeResolutionAugmentation_mem)
      (fun n c w hc hw hdc hcw ↦ ?_) c w hc hcw
  obtain ⟨x, -, hxc, hxw⟩ := exists_semifreeResolution_m_eq (n := n - 1)
    (by rwa [sub_add_cancel]) hw hdc hcw
  exact ⟨single x 1, 0, by rw [(semifreeResolution 𝒜 d 𝒩 dN).differential_single_one hA, hxc],
    by simp [hxw]⟩

/-- **The augmentation is onto.** A homogeneous `y` of degree `n` is the image of the generator
attached along `(e, y)`, where `e` is the generator attached along `(0, dN y)`. -/
theorem linearCombination_semifreeResolutionAugmentation_surjective
    (hN : IsDGLeftModule hA 𝒩 dN) :
    Function.Surjective (linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN)) := by
  intro y
  induction y using DirectSum.Decomposition.inductionOn 𝒩 with
  | zero => exact ⟨0, map_zero _⟩
  | @homogeneous n y =>
    obtain ⟨e, he, he0, hey⟩ := exists_semifreeResolution_m_eq (𝒜 := 𝒜) (d := d) (n := n + 1)
      (c := 0) (w := dN y) (zero_mem _) (hN.isHomogeneous.map_mem y.property) (map_zero _)
      (by rw [map_zero, hN.sq_zero])
    have hmem : single e 1 ∈
        rowFiniteTotalGrading 𝒜 (semifreeResolutionIndex 𝒜 d 𝒩 dN) (n + 1) := by
      simpa only [he, neg_neg] using
        single_one_mem_rowFiniteTotalGrading 𝒜 (semifreeResolutionIndex 𝒜 d 𝒩 dN) e
    obtain ⟨x, -, -, hxy⟩ := exists_semifreeResolution_m_eq hmem y.property
      (by rw [(semifreeResolution 𝒜 d 𝒩 dN).differential_single_one hA, he0])
      (by simp [hey])
    exact ⟨single x 1, by simp [hxy]⟩
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨u₁, rfl⟩ := h₁
    obtain ⟨u₂, rfl⟩ := h₂
    exact ⟨u₁ + u₂, map_add _ _ _⟩

end TauCeti
