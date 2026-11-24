/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Attach.Basic

/-!
# Towers of cell attachments

An **augmented row-finite twisted module** (`TauCeti.RowFiniteAugmentedModule`) over a
differential graded algebra `A`, with target a graded module `M` with differential `dM`, is a
row-finite twisting cocycle on a graded set of generators together with images of the generators
in `M`, of the degrees of the generators, given by a chain map. Attaching free generators along
cycles (`TauCeti.RowFiniteTwistingCocycle.attach`), with images bounding the images of their
attaching cycles, gives a new augmented module (`TauCeti.RowFiniteAugmentedModule.attach`).

Iterating from the module with no generators, one attachment at each stage `k` chosen by a rule
`step` that may depend on the stage built so far, gives a **tower of cell attachments**
(`TauCeti.RowFiniteAugmentedModule.tower`). Its union is a single augmented row-finite twisted
module on all the attached generators `Σ k, Q k (tower step k)`:

* the twisting cocycle `TauCeti.RowFiniteAugmentedModule.towerCocycle`, in which a generator
  attached at stage `k` has row its attaching cycle, so it only involves generators attached
  before stage `k`, and the row relation is well-founded: the union is semi-free;
* the augmentation `TauCeti.RowFiniteAugmentedModule.towerAugmentation`, a degree-preserving chain
  map.

Each stage embeds in the union (`TauCeti.RowFiniteAugmentedModule.towerOf`), onto the generators
attached before it, compatibly with the differentials and the augmentations. So every vector of
the union involving only generators attached before stage `k` comes from stage `k`.

This is the shape of the semi-free resolution of `TauCeti.semifreeResolution`, which attaches all
the relative cycles of each stage.

## References

* Y. Félix, S. Halperin, J.-C. Thomas, *Rational Homotopy Theory*, Graduate Texts in Mathematics
  205, Springer, 2001, Section 6 (semifree modules).
-/

public section

open Finsupp

namespace TauCeti

universe uR uA uM u

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {M : Type uM} [AddCommGroup M] [Module R M] [Module A M]
  {ℳ : ℤ → Submodule R M} {dM : M →ₗ[R] M}

variable (𝒜 d ℳ dM) in
/-- An **augmented row-finite twisted module**: a row-finite twisting cocycle on a graded set of
generators, with a degree-preserving chain map to `M`, given on the generators. -/
structure RowFiniteAugmentedModule where
  /-- The generators. -/
  P : Type u
  /-- The indices of the generators. -/
  ind : P → ℤ
  /-- The rows of the generators. -/
  m : RowFiniteTwistingCocycle 𝒜 d P ind
  /-- The images of the generators. -/
  g : P → M
  /-- The images of the generators have the degrees of the generators. -/
  g_mem : ∀ x, g x ∈ ℳ (-ind x)
  /-- The map given by the images of the generators is a chain map. -/
  g_m : ∀ x, linearCombination A g (m.m x) = dM (g x)

namespace RowFiniteAugmentedModule

/-- The data attaching new generators `Q`, of indices `indQ`, to an augmented module: their
attaching cycles `a`, of the degrees of differentials of the new generators, and their images
`c`, of the degrees of the new generators, bounding the images of the attaching cycles. -/
structure Attachment (S : RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM) {Q : Type u}
    (indQ : Q → ℤ) where
  /-- The attaching cycles. -/
  a : Q → S.P →₀ A
  /-- The attaching cycles have the degrees of differentials of the new generators. -/
  ha : ∀ q y, a q y ∈ 𝒜 (S.ind y - indQ q + 1)
  /-- The attaching vectors are cycles. -/
  hca : ∀ q, rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) S.m.m (a q) = 0
  /-- The images of the new generators. -/
  c : Q → M
  /-- The images of the new generators have their degrees. -/
  c_mem : ∀ q, c q ∈ ℳ (-indQ q)
  /-- The image of a new generator bounds the image of its attaching cycle. -/
  g_a : ∀ q, linearCombination A S.g (a q) = dM (c q)

variable (𝒜 d ℳ dM) in
/-- The augmented module with no generators. -/
@[expose] def empty : RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM where
  P := PEmpty
  ind := PEmpty.elim
  m := 0
  g := PEmpty.elim
  g_mem := nofun
  g_m := nofun

/-- **Attaching generators to an augmented module**: the rows of the new generators are their
attaching cycles, and their images are the given ones. -/
@[expose] noncomputable def attach (S : RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM)
    {Q : Type u} {indQ : Q → ℤ} (T : S.Attachment indQ) :
    RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM where
  P := S.P ⊕ Q
  ind := Sum.elim S.ind indQ
  m := S.m.attach T.a T.ha T.hca
  g := Sum.elim S.g T.c
  g_mem := by
    rintro (x | q)
    · exact S.g_mem x
    · exact T.c_mem q
  g_m := by
    rintro (x | q)
    · simpa [linearCombination_mapDomain] using S.g_m x
    · simpa [linearCombination_mapDomain] using T.g_a q

section attach

variable (S : RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM) {Q : Type u} {indQ : Q → ℤ}
  (T : S.Attachment indQ)

/-- The rows of the attached module are those of the attaching cocycle. -/
theorem attach_m : (S.attach T).m = S.m.attach T.a T.ha T.hca :=
  (rfl)

/-- The old generators keep their indices. -/
@[simp]
theorem attach_ind_inl (x : S.P) : (S.attach T).ind (.inl x) = S.ind x :=
  (rfl)

/-- The new generators have their prescribed indices. -/
@[simp]
theorem attach_ind_inr (q : Q) : (S.attach T).ind (.inr q) = indQ q :=
  (rfl)

/-- The old generators keep their images. -/
@[simp]
theorem attach_g_inl (x : S.P) : (S.attach T).g (.inl x) = S.g x :=
  (rfl)

/-- The new generators have their prescribed images. -/
@[simp]
theorem attach_g_inr (q : Q) : (S.attach T).g (.inr q) = T.c q :=
  (rfl)

end attach

variable {Q : ℕ → RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM → Type u}
  {indQ : ∀ k S, Q k S → ℤ} (step : ∀ k S, Attachment S (indQ k S))

/-- **The tower of cell attachments** chosen by `step`: stage `k + 1` attaches to stage `k` the
generators `step k (tower step k)`. -/
@[expose] noncomputable def tower : ℕ → RowFiniteAugmentedModule.{uR, uA, uM, u} 𝒜 d ℳ dM
  | 0 => empty 𝒜 d ℳ dM
  | k + 1 => (tower k).attach (step k (tower k))

/-- The tower starts from the module with no generators. -/
theorem tower_zero : tower step 0 = empty 𝒜 d ℳ dM :=
  (rfl)

/-- Stage `k + 1` of the tower attaches the generators chosen by `step` to stage `k`. -/
theorem tower_succ (k : ℕ) : tower step (k + 1) = (tower step k).attach (step k (tower step k)) :=
  (rfl)

private theorem tower_succ_m_inl (k : ℕ) (x : (tower step k).P) :
    (tower step (k + 1)).m.m (.inl x) = mapDomain Sum.inl ((tower step k).m.m x) :=
  RowFiniteTwistingCocycle.attach_m_inl _ _ _ x

private theorem tower_succ_m_inr (k : ℕ) (q : Q k (tower step k)) :
    (tower step (k + 1)).m.m (.inr q) = mapDomain Sum.inl ((step k (tower step k)).a q) :=
  RowFiniteTwistingCocycle.attach_m_inr _ _ _ q

/-- The generators of a stage, among the generators attached at all the stages. -/
def towerOf : (k : ℕ) → (tower step k).P → Σ j, Q j (tower step j)
  | 0 => PEmpty.elim
  | k + 1 => Sum.elim (towerOf k) fun q ↦ ⟨k, q⟩

/-- The old generators of stage `k + 1` are embedded as in stage `k`. -/
@[simp]
theorem towerOf_succ_inl (k : ℕ) (x : (tower step k).P) :
    towerOf step (k + 1) (.inl x) = towerOf step k x :=
  (rfl)

/-- The new generators of stage `k + 1` are the generators attached at stage `k`. -/
@[simp]
theorem towerOf_succ_inr (k : ℕ) (q : Q k (tower step k)) :
    towerOf step (k + 1) (.inr q) = ⟨k, q⟩ :=
  (rfl)

/-- The generators of stage `k` were attached at stages before `k`. -/
theorem fst_towerOf_lt : ∀ (k : ℕ) (x : (tower step k).P), (towerOf step k x).1 < k
  | 0, x => x.elim
  | k + 1, .inl x => (fst_towerOf_lt k x).trans (Nat.lt_succ_self k)
  | _ + 1, .inr _ => Nat.lt_succ_self _

theorem towerOf_injective : ∀ k : ℕ, Function.Injective (towerOf step k)
  | 0 => fun x ↦ x.elim
  | k + 1 => by
    rintro (x | q) (y | q') hxy
    · exact congrArg Sum.inl (towerOf_injective k hxy)
    · exact absurd (congrArg Sigma.fst hxy) (fst_towerOf_lt step k x).ne
    · exact absurd (congrArg Sigma.fst hxy) (fst_towerOf_lt step k y).ne'
    · cases hxy
      rfl

/-- The generators of stage `k` are the generators attached before stage `k`. -/
theorem range_towerOf : ∀ k : ℕ, Set.range (towerOf step k) = {y | y.1 < k}
  | 0 => by
    refine Set.Subset.antisymm ?_ fun y hy ↦ absurd hy (Nat.not_lt_zero _)
    rintro _ ⟨x, -⟩
    exact PEmpty.elim x
  | k + 1 => by
    ext ⟨j, q⟩
    refine ⟨fun ⟨x, hx⟩ ↦ ?_, fun hj ↦ ?_⟩
    · have hx' := fst_towerOf_lt step (k + 1) x
      rwa [hx] at hx'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨x, hx⟩ : (⟨j, q⟩ : Σ j, Q j (tower step j)) ∈ Set.range (towerOf step k) := by
          rw [range_towerOf k]
          exact hj
        exact ⟨.inl x, hx⟩
      · exact ⟨.inr q, rfl⟩

/-- The embedding of a stage preserves the indices of the generators. -/
theorem indQ_towerOf : ∀ (k : ℕ) (x : (tower step k).P),
    indQ (towerOf step k x).1 _ (towerOf step k x).2 = (tower step k).ind x
  | 0, x => x.elim
  | k + 1, .inl x => indQ_towerOf k x
  | _ + 1, .inr _ => rfl

/-- The augmentation of the union of the tower: a generator is sent to its image at the stage
where it is attached. -/
noncomputable def towerAugmentation (x : Σ k, Q k (tower step k)) : M :=
  (step x.1 _).c x.2

/-- A generator attached at stage `k` is sent to its image chosen at stage `k`. -/
@[simp]
theorem towerAugmentation_mk (k : ℕ) (q : Q k (tower step k)) :
    towerAugmentation step ⟨k, q⟩ = (step k _).c q :=
  (rfl)

private theorem towerAugmentation_towerOf : ∀ (k : ℕ) (x : (tower step k).P),
    towerAugmentation step (towerOf step k x) = (tower step k).g x
  | 0, x => x.elim
  | k + 1, .inl x => towerAugmentation_towerOf k x
  | _ + 1, .inr _ => rfl

/-- The augmentation of the union restricts to the augmentation of each stage. -/
theorem linearCombination_towerAugmentation_mapDomain (k : ℕ) (f : (tower step k).P →₀ A) :
    linearCombination A (towerAugmentation step) (mapDomain (towerOf step k) f) =
      linearCombination A (tower step k).g f := by
  rw [linearCombination_mapDomain, Function.comp_def]
  simp only [towerAugmentation_towerOf]

/-- The rows of the union of the tower, before the twisting equation is proved: a generator
attached at stage `k` has row its attaching cycle, relabelled into the union. -/
private noncomputable def towerRow (x : Σ k, Q k (tower step k)) :
    (Σ k, Q k (tower step k)) →₀ A :=
  mapDomain (towerOf step x.1) ((step x.1 _).a x.2)

private theorem towerRow_towerOf : ∀ (k : ℕ) (x : (tower step k).P),
    towerRow step (towerOf step k x) = mapDomain (towerOf step k) ((tower step k).m.m x)
  | 0, x => x.elim
  -- `towerOf (k + 1) ∘ Sum.inl` is `towerOf k` by definition, and the rows of stage `k + 1` are
  -- those of stage `k` and the attaching cycles, both relabelled along `Sum.inl`.
  | k + 1, .inl x => by
    refine (towerRow_towerOf k x).trans ?_
    rw [tower_succ_m_inl]
    exact mapDomain_comp (v := (tower step k).m.m x) (f := Sum.inl) (g := towerOf step (k + 1))
  | k + 1, .inr q => by
    rw [tower_succ_m_inr]
    exact mapDomain_comp (v := (step k (tower step k)).a q) (f := Sum.inl)
      (g := towerOf step (k + 1))

private theorem rowFiniteTwistedDifferential_towerRow_mapDomain (k : ℕ)
    (f : (tower step k).P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (towerRow step) (mapDomain (towerOf step k) f) =
      mapDomain (towerOf step k)
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (tower step k).m.m f) :=
  rowFiniteTwistedDifferential_mapDomain _ _ (towerRow_towerOf step k) f

private theorem towerRow_mem_graded (x y : Σ k, Q k (tower step k)) :
    towerRow step x y ∈ 𝒜 (indQ y.1 _ y.2 - indQ x.1 _ x.2 + 1) := by
  have hrow : (step x.1 _).a x.2 ∈
      rowFiniteTotalGrading 𝒜 (tower step x.1).ind (1 - indQ x.1 _ x.2) :=
    (mem_rowFiniteTotalGrading_iff 𝒜 _).2 fun y ↦ by
      convert (step x.1 _).ha x.2 y using 2
      ring
  have h := (mem_rowFiniteTotalGrading_iff 𝒜 _).1
    ((mapDomain_mem_rowFiniteTotalGrading_iff 𝒜 _
      (ind' := fun y : Σ k, Q k (tower step k) ↦ indQ y.1 _ y.2)
      (towerOf_injective step x.1) (indQ_towerOf step x.1)).2 hrow) y
  rw [towerRow]
  convert h using 2
  ring

/-- **The twisting cocycle of the union of the tower**: a generator attached at stage `k` has row
its attaching cycle, relabelled into the union. -/
noncomputable def towerCocycle :
    RowFiniteTwistingCocycle 𝒜 d (Σ k, Q k (tower step k)) fun x ↦ indQ x.1 _ x.2 where
  m := towerRow step
  mem_graded := towerRow_mem_graded step
  twisting x := by
    refine (mapRange_eq_sum_iff_rowFiniteTwistedDifferential_eq_zero _
      (towerRow_mem_graded step x)).2 ?_
    rw [towerRow, rowFiniteTwistedDifferential_towerRow_mapDomain, (step x.1 _).hca x.2,
      mapDomain_zero]

/-- The row of a generator attached at stage `k` is its attaching cycle, relabelled. -/
@[simp]
theorem towerCocycle_m (x : Σ k, Q k (tower step k)) :
    (towerCocycle step).m x = mapDomain (towerOf step x.1) ((step x.1 _).a x.2) :=
  (rfl)

/-- The differential of the union restricts to the differential of each stage. -/
@[simp]
theorem rowFiniteTwistedDifferential_towerCocycle_mapDomain (k : ℕ) (f : (tower step k).P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (towerCocycle step).m
        (mapDomain (towerOf step k) f) =
      mapDomain (towerOf step k)
        (rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (tower step k).m.m f) :=
  rowFiniteTwistedDifferential_towerRow_mapDomain step k f

/-- The vectors of a stage only involve the generators attached before it. -/
theorem mapDomain_towerOf_mem_supported (k : ℕ) (f : (tower step k).P →₀ A) :
    mapDomain (towerOf step k) f ∈ supported A A {y | y.1 < k} := by
  classical
  intro y hy
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (mapDomain_support hy)
  exact fst_towerOf_lt step k x

/-- The vectors of the union involving only generators attached before stage `k` come from
stage `k`. -/
theorem exists_mapDomain_towerOf_eq {k : ℕ} {f : (Σ j, Q j (tower step j)) →₀ A}
    (hf : f ∈ supported A A {y | y.1 < k}) :
    ∃ f' : (tower step k).P →₀ A, mapDomain (towerOf step k) f' = f := by
  rw [mem_supported', ← range_towerOf step k] at hf
  exact (mem_range_mapDomain_iff _ (towerOf_injective step k) f).2 hf

/-- A vector of a stage is a cycle exactly when its image in the union is. -/
theorem rowFiniteTwistedDifferential_towerCocycle_mapDomain_eq_zero_iff (k : ℕ)
    (f : (tower step k).P →₀ A) :
    rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (towerCocycle step).m
        (mapDomain (towerOf step k) f) = 0 ↔
      rowFiniteTwistedDifferential (𝒜 := 𝒜) (d := d) (tower step k).m.m f = 0 := by
  rw [rowFiniteTwistedDifferential_towerCocycle_mapDomain]
  exact (mapDomain_injective (towerOf_injective step k)).eq_iff' mapDomain_zero

/-- The row of a generator attached at stage `k` only involves generators attached before. -/
theorem towerCocycle_m_mem_supported (x : Σ k, Q k (tower step k)) :
    (towerCocycle step).m x ∈ supported A A {y | y.1 < x.1} :=
  mapDomain_towerOf_mem_supported step x.1 _

/-- **The union of the tower is semi-free**: the relation `y ∈ (m x).support` is well-founded. -/
theorem wellFounded_mem_support_towerCocycle :
    WellFounded fun y x ↦ y ∈ ((towerCocycle step).m x).support :=
  Subrelation.wf (r := InvImage (· < ·) Sigma.fst)
    (fun {_ x} hy ↦ towerCocycle_m_mem_supported step x hy) (InvImage.wf _ wellFounded_lt)

/-- The augmentation of the union preserves degrees. -/
theorem towerAugmentation_mem (x : Σ k, Q k (tower step k)) :
    towerAugmentation step x ∈ ℳ (-indQ x.1 _ x.2) :=
  (step x.1 _).c_mem x.2

/-- **The augmentation of the union is a chain map**, on the generators: the image of the row of
a generator is the differential of its image. -/
theorem linearCombination_towerAugmentation_m (x : Σ k, Q k (tower step k)) :
    linearCombination A (towerAugmentation step) ((towerCocycle step).m x) =
      dM (towerAugmentation step x) := by
  rw [towerCocycle_m, linearCombination_towerAugmentation_mapDomain]
  exact (step x.1 _).g_a x.2

end RowFiniteAugmentedModule

end TauCeti
