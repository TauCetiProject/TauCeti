/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Basic

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
involves generators of earlier stages, so the row relation is well-founded.

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

/-- A stage of the construction: a row-finite twisted module with a degree-preserving chain map
to `N`, given on the generators. -/
private structure ResolutionStage where
  /-- The generators. -/
  P : Type (max uA uN)
  /-- The indices of the generators. -/
  ind : P → ℤ
  /-- The rows of the generators. -/
  m : RowFiniteTwistingCocycle 𝒜 d P ind
  /-- The images of the generators. -/
  ε : P → N
  /-- The images of the generators have the degrees of the generators. -/
  ε_mem : ∀ x, ε x ∈ 𝒩 (-ind x)
  /-- The map given by the images of the generators is a chain map. -/
  ε_m : ∀ x, linearCombination A ε (m.m x) = dN (ε x)

namespace ResolutionStage

variable {𝒜 d 𝒩 dN}

/-- A homogeneous relative cycle `(c, w)` of the chain map of a stage: a cycle `c` of total degree
`n + 1` and an element `w` of degree `n` with `ε c = dN w`. -/
private structure Cycle (S : ResolutionStage 𝒜 d 𝒩 dN) where
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
  ε_c : linearCombination A S.ε c = dN w

variable (𝒜 d 𝒩 dN) in
/-- The stage with no generators. -/
private def zero : ResolutionStage 𝒜 d 𝒩 dN where
  P := PEmpty
  ind := PEmpty.elim
  m := 0
  ε := PEmpty.elim
  ε_mem := nofun
  ε_m := nofun

/-- The next stage: one free generator is attached along every homogeneous relative cycle, with
differential its cycle and image its element of `N`. -/
private def succ (S : ResolutionStage 𝒜 d 𝒩 dN) : ResolutionStage 𝒜 d 𝒩 dN where
  P := S.P ⊕ S.Cycle
  ind := Sum.elim S.ind fun t ↦ -t.n
  m := S.m.attach (fun t ↦ t.c)
    (fun t y ↦ by
      convert (mem_rowFiniteTotalGrading_iff 𝒜 S.ind).mp t.c_mem y using 2
      ring)
    fun t ↦ t.c_cycle
  ε := Sum.elim S.ε fun t ↦ t.w
  ε_mem := by
    rintro (x | t)
    · exact S.ε_mem x
    · simpa using t.w_mem
  ε_m := by
    rintro (x | t)
    · simpa [linearCombination_mapDomain] using S.ε_m x
    · simpa [linearCombination_mapDomain] using t.ε_c

end ResolutionStage

/-- The stages of the construction, each obtained from the previous one by attaching generators
along all of its homogeneous relative cycles. -/
private def resolutionStage : ℕ → ResolutionStage 𝒜 d 𝒩 dN
  | 0 => .zero 𝒜 d 𝒩 dN
  | k + 1 => (resolutionStage k).succ

variable {𝒜 d 𝒩 dN}

private theorem resolutionStage_succ_m_inl (k : ℕ) (x : (resolutionStage 𝒜 d 𝒩 dN k).P) :
    (resolutionStage 𝒜 d 𝒩 dN (k + 1)).m.m (.inl x) =
      mapDomain Sum.inl ((resolutionStage 𝒜 d 𝒩 dN k).m.m x) :=
  RowFiniteTwistingCocycle.attach_m_inl _ _ _ x

private theorem resolutionStage_succ_m_inr (k : ℕ) (t : (resolutionStage 𝒜 d 𝒩 dN k).Cycle) :
    (resolutionStage 𝒜 d 𝒩 dN (k + 1)).m.m (.inr t) = mapDomain Sum.inl t.c :=
  RowFiniteTwistingCocycle.attach_m_inr _ _ _ t

variable (𝒜 d 𝒩 dN)

/-! ### The resolution -/

/-- The generators of the semi-free resolution: a generator is a stage `k` together with a
homogeneous relative cycle of the chain map of that stage, along which it is attached. -/
def semifreeResolutionGenerator : Type (max uA uN) :=
  Σ k, (resolutionStage 𝒜 d 𝒩 dN k).Cycle

/-- The index of a generator of the semi-free resolution: the generator attached along a relative
cycle `(c, w)` with `w` of degree `n` has index `-n`, so that it lies in degree `n`. -/
def semifreeResolutionIndex (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) : ℤ :=
  -x.2.n

variable {𝒜 d 𝒩 dN}

/-- The generators of a stage, among the generators of the resolution. -/
private def stageEmb :
    (k : ℕ) → (resolutionStage 𝒜 d 𝒩 dN k).P → semifreeResolutionGenerator 𝒜 d 𝒩 dN
  | 0 => PEmpty.elim
  | k + 1 => Sum.elim (stageEmb k) fun t ↦ ⟨k, t⟩

/-- The generators of a stage `k` were attached at stages before `k`. -/
private theorem fst_stageEmb_lt : ∀ (k : ℕ) (x : (resolutionStage 𝒜 d 𝒩 dN k).P),
    (stageEmb k x).1 < k
  | 0, x => x.elim
  | k + 1, .inl x => (fst_stageEmb_lt k x).trans (Nat.lt_succ_self k)
  | k + 1, .inr _ => Nat.lt_succ_self k

private theorem stageEmb_injective :
    ∀ k : ℕ, Function.Injective (stageEmb (𝒜 := 𝒜) (d := d) (𝒩 := 𝒩) (dN := dN) k)
  | 0 => fun x ↦ x.elim
  | k + 1 => by
    rintro (x | t) (y | t') h
    · exact congrArg Sum.inl (stageEmb_injective k h)
    · exact absurd (congrArg Sigma.fst h) (fst_stageEmb_lt k x).ne
    · exact absurd (congrArg Sigma.fst h) (fst_stageEmb_lt k y).ne'
    · cases h
      rfl

/-- Every generator attached before stage `k` is a generator of stage `k`. -/
private theorem mem_range_stageEmb : ∀ (k : ℕ) (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN),
    x.1 < k → x ∈ Set.range (stageEmb k)
  | 0, _, hx => absurd hx (Nat.not_lt_zero _)
  | k + 1, ⟨j, t⟩, hx => by
    rcases (Nat.lt_succ_iff_lt_or_eq.mp hx) with hj | rfl
    · obtain ⟨y, hy⟩ := mem_range_stageEmb k ⟨j, t⟩ hj
      exact ⟨.inl y, hy⟩
    · exact ⟨.inr t, rfl⟩

private theorem semifreeResolutionIndex_stageEmb :
    ∀ (k : ℕ) (x : (resolutionStage 𝒜 d 𝒩 dN k).P),
      semifreeResolutionIndex 𝒜 d 𝒩 dN (stageEmb k x) = (resolutionStage 𝒜 d 𝒩 dN k).ind x
  | 0, x => x.elim
  | k + 1, .inl x => semifreeResolutionIndex_stageEmb k x
  | _ + 1, .inr _ => rfl

/-- The rows of the generators of the resolution, before the twisting equation is proved: the
generator attached along `(c, w)` at stage `k` has row `c`, relabelled into the resolution. -/
private def semifreeResolutionRow (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    semifreeResolutionGenerator 𝒜 d 𝒩 dN →₀ A :=
  mapDomain (stageEmb x.1) x.2.c

/-- Relabelling the rows of a stage gives the rows of the resolution. -/
private theorem semifreeResolutionRow_stageEmb :
    ∀ (k : ℕ) (x : (resolutionStage 𝒜 d 𝒩 dN k).P),
      semifreeResolutionRow (stageEmb k x) =
        mapDomain (stageEmb k) ((resolutionStage 𝒜 d 𝒩 dN k).m.m x)
  | 0, x => x.elim
  -- The generators of stage `k + 1` are those of stage `k`, sent along `stageEmb k`, and the
  -- new ones; `stageEmb (k + 1) ∘ Sum.inl` is `stageEmb k` by definition, so the composite
  -- relabelling `mapDomain_comp` closes both cases up to unfolding.
  | k + 1, .inl x => by
    refine (semifreeResolutionRow_stageEmb k x).trans ?_
    rw [resolutionStage_succ_m_inl]
    exact mapDomain_comp (v := (resolutionStage 𝒜 d 𝒩 dN k).m.m x) (f := Sum.inl)
      (g := stageEmb (k + 1))
  | k + 1, .inr t => by
    rw [resolutionStage_succ_m_inr]
    exact mapDomain_comp (v := t.c) (f := Sum.inl) (g := stageEmb (k + 1))

/-- The differential of the resolution restricts to the differential of each stage. -/
private theorem rowFiniteTwistedDifferential_mapDomain_stageEmb (k : ℕ)
    (f : (resolutionStage 𝒜 d 𝒩 dN k).P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) semifreeResolutionRow
        (mapDomain (stageEmb k) f) =
      mapDomain (stageEmb k)
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (resolutionStage 𝒜 d 𝒩 dN k).m.m f) :=
  rowFiniteTwistedDifferential_mapDomain _ _ (semifreeResolutionRow_stageEmb k) f

/-- The row of a generator has the total degree of a differential. -/
private theorem semifreeResolutionRow_mem_graded (x y : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    semifreeResolutionRow x y ∈
      𝒜 (semifreeResolutionIndex 𝒜 d 𝒩 dN y - semifreeResolutionIndex 𝒜 d 𝒩 dN x + 1) := by
  have h := (mem_rowFiniteTotalGrading_iff 𝒜 _).mp
    ((mapDomain_mem_rowFiniteTotalGrading_iff 𝒜 _ (stageEmb_injective x.1)
      (semifreeResolutionIndex_stageEmb x.1)).mpr x.2.c_mem) y
  rw [semifreeResolutionRow]
  convert h using 2
  simp only [semifreeResolutionIndex]
  ring

variable (𝒜 d 𝒩 dN) in
/-- **The semi-free resolution** of `N`: the twisting cocycle on the generators of all stages, in
which the generator attached along a relative cycle `(c, w)` has row `c`. -/
def semifreeResolution :
    RowFiniteTwistingCocycle 𝒜 d (semifreeResolutionGenerator 𝒜 d 𝒩 dN)
      (semifreeResolutionIndex 𝒜 d 𝒩 dN) where
  m := semifreeResolutionRow
  mem_graded := semifreeResolutionRow_mem_graded
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
      (semifreeResolutionRow_mem_graded x)).mpr ?_
    rw [semifreeResolutionRow, rowFiniteTwistedDifferential_mapDomain_stageEmb, x.2.c_cycle,
      mapDomain_zero]

variable (𝒜 d 𝒩 dN) in
/-- The augmentation of the semi-free resolution: the generator attached along a relative cycle
`(c, w)` is sent to `w`. -/
def semifreeResolutionAugmentation (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) : N :=
  x.2.w

private theorem semifreeResolutionAugmentation_stageEmb :
    ∀ (k : ℕ) (x : (resolutionStage 𝒜 d 𝒩 dN k).P),
      semifreeResolutionAugmentation 𝒜 d 𝒩 dN (stageEmb k x) = (resolutionStage 𝒜 d 𝒩 dN k).ε x
  | 0, x => x.elim
  | k + 1, .inl x => semifreeResolutionAugmentation_stageEmb k x
  | _ + 1, .inr _ => rfl

private theorem linearCombination_semifreeResolutionAugmentation_mapDomain (k : ℕ)
    (f : (resolutionStage 𝒜 d 𝒩 dN k).P →₀ A) :
    linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN) (mapDomain (stageEmb k) f) =
      linearCombination A (resolutionStage 𝒜 d 𝒩 dN k).ε f := by
  rw [linearCombination_mapDomain, Function.comp_def]
  simp only [semifreeResolutionAugmentation_stageEmb]

/-! ### The characteristic property and its consequences -/

/-- The row of the generator attached along `(c, w)` is `c`, relabelled into the resolution. -/
private theorem semifreeResolution_m (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    (semifreeResolution 𝒜 d 𝒩 dN).m x = mapDomain (stageEmb x.1) x.2.c :=
  (rfl)

/-- **The resolution is semi-free**: the row of a generator only involves generators attached at
earlier stages, so the relation `y ∈ (m x).support` is well-founded. -/
theorem wellFounded_mem_support_semifreeResolution :
    WellFounded fun y x ↦ y ∈ ((semifreeResolution 𝒜 d 𝒩 dN).m x).support := by
  classical
  refine Subrelation.wf (r := InvImage (· < ·) Sigma.fst)
    (fun {y x : semifreeResolutionGenerator 𝒜 d 𝒩 dN} hy ↦ ?_) (InvImage.wf _ wellFounded_lt)
  rw [semifreeResolution_m] at hy
  obtain ⟨y', -, rfl⟩ := Finset.mem_image.mp (mapDomain_support hy)
  exact fst_stageEmb_lt x.1 y'

/-- The augmentation preserves degrees: a generator of index `i` is sent to degree `-i`. -/
theorem semifreeResolutionAugmentation_mem (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    semifreeResolutionAugmentation 𝒜 d 𝒩 dN x ∈ 𝒩 (-semifreeResolutionIndex 𝒜 d 𝒩 dN x) := by
  rw [semifreeResolutionAugmentation, semifreeResolutionIndex, neg_neg]
  exact x.2.w_mem

/-- **The augmentation is a chain map**, on the generators: the image of the row of a generator
is the differential of its image. -/
theorem linearCombination_semifreeResolutionAugmentation_m
    (x : semifreeResolutionGenerator 𝒜 d 𝒩 dN) :
    linearCombination A (semifreeResolutionAugmentation 𝒜 d 𝒩 dN)
      ((semifreeResolution 𝒜 d 𝒩 dN).m x) = dN (semifreeResolutionAugmentation 𝒜 d 𝒩 dN x) := by
  rw [semifreeResolution_m, linearCombination_semifreeResolutionAugmentation_mapDomain]
  exact x.2.ε_c

/-- Every vector of the resolution comes from some stage. -/
private theorem exists_eq_mapDomain_stageEmb (f : semifreeResolutionGenerator 𝒜 d 𝒩 dN →₀ A) :
    ∃ (k : ℕ) (f' : (resolutionStage 𝒜 d 𝒩 dN k).P →₀ A), mapDomain (stageEmb k) f' = f := by
  classical
  refine ⟨f.support.sup fun x ↦ x.1 + 1,
    (mem_range_mapDomain_iff _ (stageEmb_injective _) f).mpr fun x hx ↦ ?_⟩
  by_contra hfx
  exact hx (mem_range_stageEmb _ x (Nat.lt_of_succ_le
    (Finset.le_sup (f := fun x ↦ x.1 + 1) (mem_support_iff.mpr hfx))))

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
  obtain ⟨k, c', rfl⟩ := exists_eq_mapDomain_stageEmb c
  refine ⟨⟨k, ⟨n, c', w, ?_, hw, ?_, ?_⟩⟩, rfl, rfl, rfl⟩
  · exact (mapDomain_mem_rowFiniteTotalGrading_iff 𝒜 _ (stageEmb_injective k)
      (semifreeResolutionIndex_stageEmb k)).mp hc
  · apply mapDomain_injective (stageEmb_injective k)
    rw [← rowFiniteTwistedDifferential_mapDomain_stageEmb, mapDomain_zero]
    exact hdc
  · rwa [← linearCombination_semifreeResolutionAugmentation_mapDomain]

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
      (c := 0) (w := dN y) (zero_mem _) (hN.isHomogeneous.map_mem y.2) (map_zero _)
      (by rw [map_zero, hN.sq_zero])
    have hmem : single e 1 ∈
        rowFiniteTotalGrading 𝒜 (semifreeResolutionIndex 𝒜 d 𝒩 dN) (n + 1) := by
      simpa only [he, neg_neg] using
        single_one_mem_rowFiniteTotalGrading 𝒜 (semifreeResolutionIndex 𝒜 d 𝒩 dN) e
    obtain ⟨x, -, -, hxy⟩ := exists_semifreeResolution_m_eq hmem y.2
      (by rw [(semifreeResolution 𝒜 d 𝒩 dN).differential_single_one hA, he0])
      (by simp [hey])
    exact ⟨single x 1, by simp [hxy]⟩
  | add y₁ y₂ h₁ h₂ =>
    obtain ⟨u₁, rfl⟩ := h₁
    obtain ⟨u₂, rfl⟩ := h₂
    exact ⟨u₁ + u₂, map_add _ _ _⟩

end TauCeti
