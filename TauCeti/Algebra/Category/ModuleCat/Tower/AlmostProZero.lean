/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Functor.ProZero
public import TauCeti.RingTheory.Almost.RootSetup

/-!
# Almost-pro-zero towers of modules

A tower is almost-pro-zero relative to an ideal `I` if, for every scalar in `I` and each target
stage, some transition into that stage is killed by the scalar. The source stage can depend on
the scalar. In particular, for a compatible system of roots it suffices to check each root
separately; requiring a common source stage for all roots would be a stronger condition.

For idempotent `I`, these towers form a Serre class. The associated morphism property consists of
maps with almost-pro-zero kernel and cokernel towers. This lets one use almost-pro-zero towers
as error terms without ever forming a category of pro-objects of almost modules.

## References

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  Definition 3.2 and Lemma 3.6.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject Opposite

namespace TauCeti.ModuleTower

universe v w u

variable {R : Type u} [CommRing R]

/-- An inverse sequence is almost-pro-zero for `I` if every scalar in `I` kills a sufficiently
late transition into each given stage. The witness is allowed to depend on both inputs. -/
def IsAlmostProZero (F : ModuleTower.{v} R) (I : Ideal R) : Prop :=
  ∀ r ∈ I, ∀ j, ∃ (i : ℕᵒᵖ) (f : i ⟶ j), r • F.map f = 0

/-- The almost-pro-zero condition in terms of the functor's morphisms. -/
theorem isAlmostProZero_def (F : ModuleTower.{v} R) (I : Ideal R) :
    F.IsAlmostProZero I ↔ ∀ r ∈ I, ∀ j, ∃ (i : ℕᵒᵖ) (f : i ⟶ j), r • F.map f = 0 :=
  Iff.rfl

/-- The almost-pro-zero condition in terms of the composite transitions of the tower. -/
theorem isAlmostProZero_iff (F : ModuleTower.{v} R) (I : Ideal R) :
    F.IsAlmostProZero I ↔ ∀ r ∈ I, ∀ n, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x, r • F.transitionOfLE h x = 0 := by
  refine ⟨fun H r hr n ↦ ?_, fun H r hr j ↦ ?_⟩
  · obtain ⟨i, f, hf⟩ := H r hr (op n)
    refine ⟨i.unop, leOfHom f.unop, fun x ↦ ?_⟩
    simpa using LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hf) x
  · obtain ⟨m, h, hm⟩ := H r hr j.unop
    refine ⟨op m, (homOfLE h).op, ?_⟩
    ext x
    simpa [← transitionOfLE_def] using hm x

/-- The scalars satisfying the almost-pro-zero transition condition form an ideal: two witnesses
can be replaced by a common later stage before adding their scalars. -/
private def proZeroScalars (F : ModuleTower.{v} R) : Ideal R where
  carrier := {r | ∀ j, ∃ (i : ℕᵒᵖ) (f : i ⟶ j), r • F.map f = 0}
  zero_mem' := fun j ↦ ⟨j, 𝟙 j, by simp⟩
  add_mem' := by
    intro a b ha hb j
    obtain ⟨i, f, hf⟩ := ha j
    obtain ⟨k, g, hg⟩ := hb j
    let s : ℕᵒᵖ := op (max i.unop k.unop)
    let fi : s ⟶ i := (homOfLE (le_max_left i.unop k.unop)).op
    let fk : s ⟶ k := (homOfLE (le_max_right i.unop k.unop)).op
    refine ⟨s, fi ≫ f, ?_⟩
    have hfa : a • F.map (fi ≫ f) = 0 := by simp [← Linear.comp_smul, hf]
    have hgb : b • F.map (fk ≫ g) = 0 := by simp [← Linear.comp_smul, hg]
    rw [add_smul, hfa, Subsingleton.elim (fi ≫ f) (fk ≫ g), hgb, add_zero]
  smul_mem' := by
    intro a b hb j
    obtain ⟨i, f, hf⟩ := hb j
    exact ⟨i, f, by rw [smul_eq_mul, mul_smul, hf, smul_zero]⟩

/-- To check almost-pro-vanishing for a generated ideal, test each generator separately. -/
theorem isAlmostProZero_span_iff (F : ModuleTower.{v} R) (s : Set R) :
    F.IsAlmostProZero (Ideal.span s) ↔ ∀ r ∈ s, ∀ n, ∃ (m : ℕ) (h : n ≤ m),
      ∀ x, r • F.transitionOfLE h x = 0 := by
  refine ⟨fun H r hr ↦ (isAlmostProZero_iff F _).mp H r (Ideal.subset_span hr), fun H ↦ ?_⟩
  have hs : Ideal.span s ≤ proZeroScalars F := Ideal.span_le.mpr fun r hr ↦ by
    intro j
    obtain ⟨m, h, hm⟩ := H r hr j.unop
    refine ⟨op m, (homOfLE h).op, ?_⟩
    ext x
    simpa [← transitionOfLE_def] using hm x
  exact hs

/-- For a compatible root system it suffices to kill transitions by one root at a time. -/
theorem isAlmostProZero_ofCompatibleRoots_iff (F : ModuleTower.{v} R) {p : ℕ} (hp : 2 ≤ p)
    {t : ℕ → R} (ht : ∀ k, t (k + 1) ^ p = t k) :
    F.IsAlmostProZero (Almost.BasicSetup.ofCompatibleRoots hp ht).ideal ↔
      ∀ k n, ∃ (m : ℕ) (h : n ≤ m), ∀ x, t k • F.transitionOfLE h x = 0 := by
  rw [Almost.BasicSetup.ofCompatibleRoots_ideal, isAlmostProZero_span_iff]
  exact Set.forall_mem_range

/-- An ordinary pro-zero tower is almost-pro-zero for every ideal. -/
theorem isAlmostProZero_of_isProZero {F : ModuleTower.{v} R} (hF : F.IsProZero) (I : Ideal R) :
    F.IsAlmostProZero I := by
  intro r _ j
  obtain ⟨i, f, hf⟩ := (Functor.isProZero_iff F).mp hF j
  exact ⟨i, f, by simp [hf]⟩

/-- For the unit ideal, almost-pro-zero is ordinary pro-zero. -/
@[simp]
theorem isAlmostProZero_top_iff (F : ModuleTower.{v} R) :
    F.IsAlmostProZero (⊤ : Ideal R) ↔ F.IsProZero := by
  refine ⟨fun H ↦ (Functor.isProZero_iff F).mpr fun j ↦ ?_, fun H ↦
    isAlmostProZero_of_isProZero H _⟩
  simpa using H 1 Submodule.mem_top j

/-- Every tower whose terms are annihilated by `I` is almost-pro-zero for `I`. -/
theorem isAlmostProZero_of_isTorsionBySet {F : ModuleTower.{v} R} {I : Ideal R}
    (hF : ∀ n, Module.IsTorsionBySet R (F.obj (op n)) (I : Set R)) : F.IsAlmostProZero I := by
  refine (isAlmostProZero_iff F I).mpr fun r hr n ↦ ⟨n, le_rfl, fun x ↦ ?_⟩
  simpa using hF n (x := x) (a := ⟨r, hr⟩)

/-- A scalar kills a sufficiently late transition into every stage exactly when the inclusion of
its torsion subtower is a pro-isomorphism. The subtower is the kernel of scalar multiplication. -/
theorem isAlmostProZero_iff_forall_proIsomorphisms {F : ModuleTower.{v} R} {I : Ideal R} :
    F.IsAlmostProZero I ↔ ∀ r ∈ I,
      Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) (kernel.ι (r • 𝟙 F)) := by
  refine forall₂_congr fun r _ ↦ ?_
  let μ : F ⟶ F := r • 𝟙 F
  rw [Functor.proIsomorphisms_iff,
    and_iff_right (Functor.isProZero_of_isZero (isZero_kernel_of_mono (kernel.ι μ))),
    Functor.isProZero_iff]
  refine forall_congr' fun j ↦ exists_congr fun i ↦ exists_congr fun f ↦ ?_
  let q := Abelian.coimage.π μ
  let a := Abelian.factorThruCoimage μ
  have h (k : ℕᵒᵖ) : q.app k ≫ a.app k = r • 𝟙 (F.obj k) := by
    simpa only [q, a, μ, NatTrans.comp_app, NatTrans.app_smul, NatTrans.id_app] using
      NatTrans.congr_app (Abelian.coimage.fac μ) k
  have he : q.app i ≫ (Abelian.coimage μ).map f ≫ a.app j = r • F.map f := by
    rw [← Category.assoc, ← q.naturality, Category.assoc, h]
    simp
  have hc : (Abelian.coimage μ).map f = 0 ↔
      q.app i ≫ (Abelian.coimage μ).map f ≫ a.app j = 0 := by
    simp only [← Category.assoc, ← zero_comp (f := a.app j), cancel_mono,
      ← comp_zero (f := q.app i), cancel_epi]
  exact he ▸ hc.symm

/-- Almost-pro-vanishing is unchanged by cofinal monotone reindexing of a tower. -/
theorem isAlmostProZero_monotone_comp_iff (F : ModuleTower.{v} R) (I : Ideal R) {φ : ℕ → ℕ}
    (hφ : Monotone φ) (hcof : ∀ n, ∃ k, n ≤ φ k) :
    IsAlmostProZero (hφ.functor.op ⋙ F) I ↔ F.IsAlmostProZero I := by
  refine ⟨fun H r hr j ↦ ?_, fun H r hr j ↦ ?_⟩
  · obtain ⟨k, hk⟩ := hcof j.unop
    obtain ⟨i, f, hf⟩ := H r hr (op k)
    refine ⟨op (φ i.unop), hφ.functor.op.map f ≫ (homOfLE hk).op, ?_⟩
    rw [F.map_comp, ← Linear.smul_comp]
    rw [Functor.comp_map] at hf
    simp only [hf, zero_comp]
  · obtain ⟨i, f, hf⟩ := H r hr (hφ.functor.op.obj j)
    obtain ⟨k, hk⟩ := hcof i.unop
    let k' := max k j.unop
    let g : op k' ⟶ j := (homOfLE (le_max_right k j.unop)).op
    let a : op (φ k') ⟶ i := (homOfLE (hk.trans (hφ (le_max_left k j.unop)))).op
    refine ⟨op k', g, ?_⟩
    rw [Functor.comp_map, Subsingleton.elim (hφ.functor.op.map g) (a ≫ f), F.map_comp,
      ← Linear.comp_smul, hf, comp_zero]

/-- For an idempotent ideal the almost-pro-zero towers form a Serre class. -/
theorem isSerreClass_isAlmostProZero (I : Ideal R) (hI : IsIdempotentElem I) :
    ObjectProperty.IsSerreClass (fun F : ModuleTower.{v} R ↦ F.IsAlmostProZero I) where
  exists_zero := ⟨0, isZero_zero _, isAlmostProZero_of_isProZero Functor.isProZero_zero I⟩
  prop_of_mono {X Y} f _ hY r hr j := by
    obtain ⟨i, g, hg⟩ := hY r hr j
    refine ⟨i, g, (cancel_mono (f.app j)).mp ?_⟩
    rw [Linear.smul_comp, f.naturality, ← Linear.comp_smul, hg, comp_zero, zero_comp]
  prop_of_epi {X Y} f _ hX r hr j := by
    obtain ⟨i, g, hg⟩ := hX r hr j
    refine ⟨i, g, (cancel_epi (f.app i)).mp ?_⟩
    rw [Linear.comp_smul, ← f.naturality, ← Linear.smul_comp, hg, zero_comp, comp_zero]
  prop_X₂_of_shortExact {S} hS h₁ h₃ r hr := by
    -- Test products of scalars in the ideal; choose the stage for `X₁` before that for `X₃`.
    have hr' : r ∈ I * I := by rwa [hI.eq]
    refine Submodule.mul_induction_on (M := I) (N := I)
      (C := fun a ↦ a ∈ proZeroScalars S.X₂) hr' ?_ (fun _ _ ↦ (proZeroScalars _).add_mem)
    intro a ha b hb j
    obtain ⟨i, f, hf⟩ := h₁ a ha j
    obtain ⟨k, g, hg⟩ := h₃ b hb i
    have hSi := hS.map_of_exact ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj i)
    have := hSi.mono_f
    have hz : (b • S.X₂.map g) ≫ S.g.app i = 0 := by
      rw [Linear.smul_comp, S.g.naturality, ← Linear.comp_smul, hg, comp_zero]
    let l := hSi.exact.lift (b • S.X₂.map g) hz
    have hl : l ≫ S.f.app i = b • S.X₂.map g := hSi.exact.lift_f _ hz
    refine ⟨k, g ≫ f, ?_⟩
    calc
      (a * b) • S.X₂.map (g ≫ f) = (b • S.X₂.map g) ≫ (a • S.X₂.map f) := by
        simp [mul_smul, S.X₂.map_comp, smul_comm a b]
      _ = l ≫ (a • S.X₁.map f) ≫ S.f.app j := by
        rw [← hl, Category.assoc, Linear.comp_smul, ← S.f.naturality, ← Linear.smul_comp]
      _ = 0 := by rw [hf, zero_comp, comp_zero]

/-- Almost-pro-isomorphisms: the maps whose kernel and cokernel towers are almost-pro-zero. -/
def almostProIsomorphisms (I : Ideal R) : MorphismProperty (ModuleTower.{v} R) :=
  fun _ _ f ↦ (kernel f).IsAlmostProZero I ∧ (cokernel f).IsAlmostProZero I

/-- Test an almost-pro-isomorphism on its kernel and cokernel towers. -/
theorem almostProIsomorphisms_iff (I : Ideal R) {F G : ModuleTower.{v} R} (f : F ⟶ G) :
    almostProIsomorphisms I f ↔ (kernel f).IsAlmostProZero I ∧ (cokernel f).IsAlmostProZero I :=
  Iff.rfl

/-- Register the Serre class when idempotence is available to typeclass inference. -/
instance isSerreClass_isAlmostProZero_of_fact (I : Ideal R) [Fact (IsIdempotentElem I)] :
    ObjectProperty.IsSerreClass (fun F : ModuleTower.{v} R ↦ F.IsAlmostProZero I) :=
  isSerreClass_isAlmostProZero I Fact.out

/-- For idempotent `I`, almost-pro-isomorphisms are isomorphisms modulo the Serre class of
almost-pro-zero towers. -/
theorem almostProIsomorphisms_eq_isoModSerre (I : Ideal R) [Fact (IsIdempotentElem I)] :
    almostProIsomorphisms.{v} I =
      ObjectProperty.isoModSerre (fun F : ModuleTower.{v} R ↦ F.IsAlmostProZero I) := by
  ext F G f
  rw [almostProIsomorphisms_iff, ObjectProperty.isoModSerre_iff, ObjectProperty.monoModSerre_iff,
    ObjectProperty.epiModSerre_iff]

instance (I : Ideal R) [Fact (IsIdempotentElem I)] :
    (almostProIsomorphisms.{v} I).IsMultiplicative := by
  rw [almostProIsomorphisms_eq_isoModSerre]
  infer_instance

instance (I : Ideal R) [Fact (IsIdempotentElem I)] :
    (almostProIsomorphisms.{v} I).HasTwoOutOfThreeProperty := by
  rw [almostProIsomorphisms_eq_isoModSerre]
  infer_instance

/-- A linear functor preserves almost-pro-zero towers, without an exactness hypothesis. -/
theorem IsAlmostProZero.comp {F : ModuleTower.{v} R} {I : Ideal R} (hF : F.IsAlmostProZero I)
    (G : ModuleCat.{v} R ⥤ ModuleCat.{w} R) [G.Linear R] :
    IsAlmostProZero (F ⋙ G) I := by
  intro r hr j
  obtain ⟨i, f, hf⟩ := hF r hr j
  have hz : G.map (0 : F.obj i ⟶ F.obj j) = 0 := by
    simpa only [zero_smul] using G.map_smul (0 : R) (F.map f)
  exact ⟨i, f, by rw [Functor.comp_map, ← G.map_smul, hf, hz]⟩

end TauCeti.ModuleTower
