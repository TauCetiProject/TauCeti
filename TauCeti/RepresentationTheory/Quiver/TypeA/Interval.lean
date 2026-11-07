/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Quiver.Line
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Interval representations of a linearly oriented quiver

The interval representation `LineQuiver.intervalRep k a b` puts a copy of `k` at the vertices
in `[a,b]`, zero elsewhere, and identity maps between adjacent nonzero spaces. Its dimension
vector is the indicator of `[a,b]`. For `a ≤ b`, every endomorphism is scalar, so the
representation is indecomposable, and its endpoints are determined by its isomorphism class.
The construction and the scalar-endomorphism theorem work over any commutative ring; the
dimension and indecomposability statements are over a field.

These are the explicit indecomposable objects used to describe the triangular
Auslander–Reiten mesh of a linearly oriented type-A quiver. This file constructs the objects
and proves the brick and distinctness properties; it does not assert their exhaustiveness.

## References

* R. Schiffler, *Quiver Representations*, Chapters 1 and 3.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.LineQuiver

variable (k : Type*) {n : ℕ} (a b : LineQuiver n)

section Ring

variable [CommRing k]

private def intervalSpace (i : LineQuiver n) : Submodule k k :=
  if a ≤ i ∧ i ≤ b then ⊤ else ⊥

private theorem intervalSpace_eq_zero {i : LineQuiver n} (hi : ¬ (a ≤ i ∧ i ≤ b))
    (x : intervalSpace k a b i) : x = 0 := by
  apply Subtype.ext
  have hx := x.property
  simpa [intervalSpace, hi] using hx

private def intervalMap {i j : LineQuiver n} :
    intervalSpace k a b i →ₗ[k] intervalSpace k a b j :=
  if hj : a ≤ j ∧ j ≤ b then
    (LinearMap.id : k →ₗ[k] k).codRestrict (intervalSpace k a b j)
      (by intro x; simp [intervalSpace, hj]) |>.comp (intervalSpace k a b i).subtype
  else 0

private theorem coe_intervalMap {i j : LineQuiver n} (x : intervalSpace k a b i) :
    ((intervalMap k a b (j := j) x : intervalSpace k a b j) : k) =
      if a ≤ j ∧ j ≤ b then (x : k) else 0 := by
  dsimp [intervalMap]
  split <;> rfl

/-- The representation supported on the closed interval `[a,b]` of the line quiver, with
free rank-one modules and identity maps on its support. If `b < a`, it is zero. -/
def intervalRep : QuiverRep k (LineQuiver n) where
  obj i := ModuleCat.of k (intervalSpace k a b i)
  map _ := ModuleCat.ofHom (intervalMap k a b)
  map_id := fun (i : LineQuiver n) ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.id_apply, coe_intervalMap]
    split
    · rfl
    · rename_i hi
      rw [intervalSpace_eq_zero k a b hi x]
      rfl
  map_comp := fun {i j l : LineQuiver n} p q ↦ by
    have hij := le_of_path p
    have hjl := le_of_path q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, coe_intervalMap]
    by_cases hl : a ≤ l ∧ l ≤ b
    · by_cases hj : a ≤ j ∧ j ≤ b
      · simp [hl, hj]
      · have hi : ¬ (a ≤ i ∧ i ≤ b) := by
          intro hi
          exact hj ⟨hi.1.trans hij, hjl.trans hl.2⟩
        rw [intervalSpace_eq_zero k a b hi x]
        simp [hl, hj]
    · simp [hl]

/-- The vertex spaces of an interval representation, realized as submodules of the base ring. -/
theorem intervalRep_obj (i : LineQuiver n) :
    (intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i) =
      ModuleCat.of k ↥(if a ≤ i ∧ i ≤ b then (⊤ : Submodule k k) else ⊥) := (rfl)

/-- The distinguished generator at a vertex of the interval: one on the support and zero
off the support. -/
def intervalGenerator (i : LineQuiver n) :
    (intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i) :=
  ⟨if a ≤ i ∧ i ≤ b then 1 else 0, by
    by_cases hi : a ≤ i ∧ i ≤ b <;> simp [intervalSpace, hi]⟩

private theorem coe_intervalGenerator (i : LineQuiver n) :
    Subtype.val (intervalGenerator k a b i) = if a ≤ i ∧ i ≤ b then 1 else 0 := (rfl)

/-- The scalar coordinate of a vector in a vertex space of the interval representation. -/
def intervalRepCoord (i : LineQuiver n) :
    (intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i) →ₗ[k] k :=
  (intervalSpace k a b i).subtype

/-- A vector in an interval's vertex space is determined by its scalar coordinate. -/
theorem intervalRepCoord_injective (i : LineQuiver n) :
    Function.Injective (intervalRepCoord k a b i) := Subtype.val_injective

/-- The interval generator has coordinate one on the support and zero off the support. -/
@[simp]
theorem intervalRepCoord_generator (i : LineQuiver n) :
    intervalRepCoord k a b i (intervalGenerator k a b i) =
      if a ≤ i ∧ i ≤ b then 1 else 0 := (rfl)

/-- Off its support, an interval representation has zero vertex space. -/
theorem isZero_intervalRep_obj {i : LineQuiver n} (hi : ¬ (a ≤ i ∧ i ≤ b)) :
    Limits.IsZero ((intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i)) := by
  rw [intervalRep_obj, ite_eq_right_iff.mpr (fun h ↦ (hi h).elim)]
  exact ModuleCat.isZero_of_subsingleton _

/-- The distinguished generator is zero outside the interval. -/
@[simp]
theorem intervalGenerator_eq_zero {i : LineQuiver n} (hi : ¬ (a ≤ i ∧ i ≤ b)) :
    intervalGenerator k a b i = 0 := by
  exact intervalSpace_eq_zero k a b hi _

/-- On its support, the distinguished generator of an interval is nonzero. -/
theorem intervalGenerator_ne_zero [Nontrivial k] {i : LineQuiver n} (hi : a ≤ i ∧ i ≤ b) :
    intervalGenerator k a b i ≠ 0 := by
  intro h
  have h' : Subtype.val (intervalGenerator k a b i) = (0 : k) := congrArg Subtype.val h
  simp [coe_intervalGenerator, hi] at h'

/-- Scalar coordinates reconstruct vectors from the distinguished interval generator,
including in the zero spaces outside the interval. -/
@[simp]
theorem intervalRepCoord_smul_generator (i : LineQuiver n)
    (x : (intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i)) :
    intervalRepCoord k a b i x • intervalGenerator k a b i = x := by
  by_cases hi : a ≤ i ∧ i ≤ b
  · apply Subtype.ext
    -- The bundled vertex module hides its scalar action from rewriting; retype it in `k`.
    change x.val * (if a ≤ i ∧ i ≤ b then 1 else 0) = x.val
    simp only [ite_eq_left hi, mul_one]
  · have hx := intervalSpace_eq_zero k a b hi x
    subst x
    exact zero_smul k (intervalGenerator k a b i)

/-- A path carries the interval generator to the generator at its target precisely when
both endpoints lie in the interval; otherwise its value is zero. -/
@[simp]
theorem intervalRep_map_generator {i j : LineQuiver n} (p : Quiver.Path i j) :
    (intervalRep k a b).map p (intervalGenerator k a b i) =
      if a ≤ i ∧ j ≤ b then intervalGenerator k a b j else 0 := by
  have hij := le_of_path p
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hj : a ≤ j ∧ j ≤ b
    · rw [ite_eq_left ⟨hi.1, hj.2⟩]
      apply Subtype.ext
      exact (coe_intervalMap k a b (j := j) (intervalGenerator k a b i)).trans (by
        simp only [coe_intervalGenerator, ite_eq_left hi, ite_eq_left hj])
    · have h : ¬ (a ≤ i ∧ j ≤ b) := fun h ↦ hj ⟨h.1.trans hij, h.2⟩
      rw [ite_eq_right h]
      exact intervalSpace_eq_zero k a b hj _
  · have h : ¬ (a ≤ i ∧ j ≤ b) := fun h ↦ hi ⟨h.1, hij.trans h.2⟩
    rw [ite_eq_right h, intervalGenerator_eq_zero k a b hi]
    exact map_zero ((intervalRep k a b).map p).hom

/-- An interval representation over a nonzero coefficient ring is zero exactly when
its interval is empty. -/
@[simp]
theorem isZero_intervalRep_iff [Nontrivial k] :
    Limits.IsZero (intervalRep k a b) ↔ b < a := by
  constructor
  · intro h
    apply lt_of_not_ge
    intro hab
    have hz := (Functor.isZero_iff _).mp h a
    exact intervalGenerator_ne_zero k a b ⟨le_rfl, hab⟩
      ((ModuleCat.subsingleton_of_isZero hz).elim _ _)
  · intro h
    refine (Functor.isZero_iff _).mpr (fun (i : LineQuiver n) ↦ ?_)
    exact isZero_intervalRep_obj k a b (fun hi ↦ (not_le.mpr h) (hi.1.trans hi.2))

variable {k a b}

/-- A morphism out of an interval is determined by the image of the generator at its left
endpoint. This also holds for the zero representation associated to an empty interval. -/
theorem intervalRep_hom_ext {M : QuiverRep k (LineQuiver n)}
    {f g : intervalRep k a b ⟶ M}
    (h : f.app ((Paths.of (LineQuiver n)).obj a) (intervalGenerator k a b a) =
      g.app ((Paths.of (LineQuiver n)).obj a) (intervalGenerator k a b a)) :
    f = g := by
  apply NatTrans.ext
  funext (i : LineQuiver n)
  -- Keep evaluation at a vertex behind the canonical inclusion into the path category.
  change f.app ((Paths.of (LineQuiver n)).obj i) = g.app ((Paths.of (LineQuiver n)).obj i)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [← intervalRepCoord_smul_generator k a b i x]
  simp only [map_smul]
  congr 1
  by_cases hi : a ≤ i ∧ i ≤ b
  · obtain ⟨p⟩ := (nonempty_path_iff_le a i).mpr hi.1
    have hf : f.app i ((intervalRep k a b).map p (intervalGenerator k a b a)) =
        M.map p (f.app a (intervalGenerator k a b a)) :=
      ConcreteCategory.congr_hom (f.naturality p) (intervalGenerator k a b a)
    have hg : g.app i ((intervalRep k a b).map p (intervalGenerator k a b a)) =
        M.map p (g.app a (intervalGenerator k a b a)) :=
      ConcreteCategory.congr_hom (g.naturality p) (intervalGenerator k a b a)
    simp only [intervalRep_map_generator, le_refl, true_and, ite_eq_left hi.2] at hf hg
    exact hf.trans ((congrArg (M.map p) h).trans hg.symm)
  · simp [intervalGenerator_eq_zero k a b hi]

/-- Every endomorphism of an interval representation is scalar multiplication. -/
theorem intervalRep_end_eq_smul_id (f : intervalRep k a b ⟶ intervalRep k a b) :
    ∃ c : k, f = c • 𝟙 (intervalRep k a b) := by
  refine ⟨intervalRepCoord k a b a (f.app a (intervalGenerator k a b a)),
    intervalRep_hom_ext ?_⟩
  exact (intervalRepCoord_smul_generator k a b a _).symm

end Ring

section Field

variable [Field k]

/-- Every vertex space of an interval representation is finite-dimensional. -/
instance finiteDimensional_intervalRep_obj (i : LineQuiver n) :
    FiniteDimensional k ((intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i)) :=
  inferInstanceAs (FiniteDimensional k (intervalSpace k a b i))

/-- The vertex dimension of an interval representation is the indicator of its support. -/
@[simp]
theorem finrank_intervalRep_obj (i : LineQuiver n) :
    Module.finrank k ((intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i)) =
      if a ≤ i ∧ i ≤ b then 1 else 0 := by
  split_ifs with hi
  · exact (finrank_eq_one_iff_of_ne_zero' (intervalGenerator k a b i)
      (intervalGenerator_ne_zero k a b hi)).mpr (fun x ↦
        ⟨intervalRepCoord k a b i x, intervalRepCoord_smul_generator k a b i x⟩)
  · let := ModuleCat.subsingleton_of_isZero (isZero_intervalRep_obj k a b hi)
    exact Module.finrank_zero_of_subsingleton (R := k)
      (M := (intervalRep k a b).obj ((Paths.of (LineQuiver n)).obj i))

variable {k a b}

/-- A nonempty interval is a brick: its endomorphism space has dimension one over `k`. -/
@[simp]
theorem finrank_end_intervalRep (hab : a ≤ b) :
    Module.finrank k (intervalRep k a b ⟶ intervalRep k a b) = 1 := by
  have hid : 𝟙 (intervalRep k a b) ≠ 0 := by
    intro h
    have h' := congrArg (fun f : intervalRep k a b ⟶ intervalRep k a b ↦
      (f.app a).hom (intervalGenerator k a b a)) h
    exact intervalGenerator_ne_zero k a b ⟨le_rfl, hab⟩ h'
  exact (finrank_eq_one_iff_of_ne_zero' _ hid).mpr (fun f ↦
    (intervalRep_end_eq_smul_id f).imp fun _ h ↦ h.symm)

/-- Every nonempty interval representation is indecomposable, over any coefficient field. -/
theorem indecomposable_intervalRep (hab : a ≤ b) : Indecomposable (intervalRep k a b) :=
  indecomposable_of_finrank_end_eq_one (finrank_end_intervalRep hab)

/-- Two nonempty interval representations are isomorphic exactly when both endpoints agree. -/
@[simp]
theorem nonempty_iso_intervalRep_iff {c d : LineQuiver n} (hab : a ≤ b) (hcd : c ≤ d) :
    Nonempty (intervalRep k a b ≅ intervalRep k c d) ↔ a = c ∧ b = d := by
  refine ⟨fun ⟨e⟩ ↦ ?_, fun ⟨rfl, rfl⟩ ↦ ⟨Iso.refl _⟩⟩
  have hdim := congrFun (dimVector_eq_of_iso e)
  have ha := hdim a
  have hb := hdim b
  have hc := hdim c
  have hd := hdim d
  simp only [dimVector_apply, finrank_intervalRep_obj] at ha hb hc hd
  have hac : c ≤ a ∧ a ≤ d := by simpa [hab] using ha.symm
  have hbd : c ≤ b ∧ b ≤ d := by simpa [hab] using hb.symm
  have hca : a ≤ c ∧ c ≤ b := by simpa [hcd] using hc
  have hdb : a ≤ d ∧ d ≤ b := by simpa [hcd] using hd
  exact ⟨le_antisymm hca.1 hac.1, le_antisymm hbd.2 hdb.2⟩

end Field

end TauCeti.LineQuiver
