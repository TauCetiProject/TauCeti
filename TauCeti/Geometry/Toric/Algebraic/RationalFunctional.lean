/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import Mathlib.Data.Rat.Cast.Order

/-!
# Rational functionals of an integral lattice

A rational functional is a rational multiple of the real extension of one
integral character. Finite sums have this form by clearing denominators. The
lattice is the actual scalar-extension datum `TauCeti.Toric.IsIntegralLattice`,
passed as a term rather than a typeclass. These functionals describe rational
normals to affine polyhedra, independently of their real offsets.

Adapted from `Mei/Geometry/Toric/Algebraic/RationalFunctional.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei),
commit `61509bfe75ce943898bc99cfa509fb40bb78c614` (Apache 2.0).
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}

/-- A rational multiple of the real extension of an integral character. -/
def IsRationalFunctional (h : IsIntegralLattice i) (f : Module.Dual ℝ V) : Prop :=
  ∃ (q : ℚ) (m : Module.Dual ℤ N), f = (q : ℝ) • h.realCharacter m.toAddMonoidHom

namespace IsRationalFunctional

variable {h : IsIntegralLattice i} {f g : Module.Dual ℝ V}

/-- The definition is precisely a rational multiple of an integral character. -/
theorem iff_exists_character : IsRationalFunctional h f ↔
    ∃ (q : ℚ) (m : Module.Dual ℤ N), f = (q : ℝ) • h.realCharacter m.toAddMonoidHom :=
  Iff.rfl

/-- The zero functional is rational. -/
@[simp]
theorem zero (h : IsIntegralLattice i) : IsRationalFunctional h 0 :=
  ⟨0, 0, by simp⟩

/-- The real extension of an integral character is rational. -/
theorem realCharacter (h : IsIntegralLattice i) (m : Module.Dual ℤ N) :
    IsRationalFunctional h (h.realCharacter m.toAddMonoidHom) :=
  ⟨1, m, by simp⟩

/-- Addition preserves rational functionals, by a common denominator. -/
theorem add (hf : IsRationalFunctional h f) (hg : IsRationalFunctional h g) :
    IsRationalFunctional h (f + g) := by
  obtain ⟨q, m, rfl⟩ := hf
  obtain ⟨r, n, rfl⟩ := hg
  let a : ℤ := q.num * r.den
  let b : ℤ := r.num * q.den
  refine ⟨(q.den * r.den : ℚ)⁻¹, a • m + b • n, ?_⟩
  have hchar : h.realCharacter (a • m + b • n).toAddMonoidHom =
      (a : ℝ) • h.realCharacter m.toAddMonoidHom +
        (b : ℝ) • h.realCharacter n.toAddMonoidHom := by
    symm
    apply h.eq_realCharacter
    intro n
    simp
  rw [hchar, smul_add, smul_smul, smul_smul]
  have hqden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hrden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hq : (q : ℝ) = q.num / q.den := Rat.cast_def q
  have hr : (r : ℝ) = r.num / r.den := Rat.cast_def r
  congr 1 <;> congr 1 <;> push_cast [a, b] <;>
    simp only [hq, hr] <;> field_simp

/-- Negating a rational functional preserves rationality. -/
theorem neg (hf : IsRationalFunctional h f) : IsRationalFunctional h (-f) := by
  obtain ⟨q, m, rfl⟩ := hf
  refine ⟨-q, m, ?_⟩
  ext x
  simp

/-- Subtracting rational functionals preserves rationality. -/
theorem sub (hf : IsRationalFunctional h f) (hg : IsRationalFunctional h g) :
    IsRationalFunctional h (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- Multiplication by a rational scalar preserves rationality. -/
theorem rat_smul (hf : IsRationalFunctional h f) (q : ℚ) :
    IsRationalFunctional h ((q : ℝ) • f) := by
  obtain ⟨r, m, rfl⟩ := hf
  exact ⟨q * r, m, by simp [smul_smul]⟩

/-- Every finite sum of rational functionals is rational. -/
theorem sum {ι : Type*} (s : Finset ι) (f : ι → Module.Dual ℝ V)
    (hf : ∀ j ∈ s, IsRationalFunctional h (f j)) :
    IsRationalFunctional h (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
    rw [Finset.sum_insert hjs]
    exact (hf j (Finset.mem_insert_self _ _)).add
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)))

/-- A rational functional takes rational values on lattice points. -/
theorem exists_rat_apply (hf : IsRationalFunctional h f) (n : N) :
    ∃ q : ℚ, f (i n) = (q : ℝ) := by
  obtain ⟨q, m, rfl⟩ := hf
  exact ⟨q * (m n : ℚ), by simp⟩

section Maps

variable {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {h' : IsIntegralLattice i'} {f' : Module.Dual ℝ V'}

/-- Pullback by a real-linear map compatible with an integral lattice map
preserves rational functionals. -/
theorem comp (hf : IsRationalFunctional h' f') (h : IsIntegralLattice i)
    (u : N →+ N') (T : V →ₗ[ℝ] V') (hT : ∀ n, T (i n) = i' (u n)) :
    IsRationalFunctional h (f'.comp T) := by
  obtain ⟨q, m, rfl⟩ := hf
  refine ⟨q, m.comp u.toIntLinearMap, ?_⟩
  rw [LinearMap.smul_comp, ← h.realCharacter_comp h' u T hT]
  rfl

/-- The canonical real extension of an integral map preserves rationality
under pullback. -/
theorem comp_extend (hf : IsRationalFunctional h' f') (h : IsIntegralLattice i)
    (u : N →+ N') : IsRationalFunctional h (f'.comp (h.extend i' u)) :=
  hf.comp h u (h.extend i' u) (fun n => h.extend_apply i' u n)

end Maps

end IsRationalFunctional

/-- A real-linear map is rational when it pulls rational functionals back to
rational functionals. -/
def IsRationalLinearMap {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
    {i' : N' →+ V'} (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (T : V →ₗ[ℝ] V') : Prop :=
  ∀ f : Module.Dual ℝ V', IsRationalFunctional h' f → IsRationalFunctional h (f.comp T)

/-- Rationality of a linear map is precisely preservation of rational functionals
under pullback. -/
theorem isRationalLinearMap_iff {N' V' : Type*} [AddCommGroup N'] [AddCommGroup V']
    [Module ℝ V'] {i' : N' →+ V'} (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (T : V →ₗ[ℝ] V') :
    IsRationalLinearMap h h' T ↔
      ∀ f : Module.Dual ℝ V', IsRationalFunctional h' f → IsRationalFunctional h (f.comp T) :=
  Iff.rfl

namespace IsRationalLinearMap

variable {N' N'' V' V'' : Type*} [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V'] [Module ℝ V'']
  {i' : N' →+ V'} {i'' : N'' →+ V''}
  {h : IsIntegralLattice i} {h' : IsIntegralLattice i'} {h'' : IsIntegralLattice i''}

/-- A rational linear map pulls each rational functional back to a rational functional. -/
theorem map_functional {T : V →ₗ[ℝ] V'} (hT : IsRationalLinearMap h h' T)
    {f : Module.Dual ℝ V'} (hf : IsRationalFunctional h' f) :
    IsRationalFunctional h (f.comp T) :=
  hT f hf

/-- The identity real-linear map is rational. -/
theorem id (h : IsIntegralLattice i) : IsRationalLinearMap h h LinearMap.id := by
  intro f hf
  simpa using hf

/-- Composites of rational real-linear maps are rational. -/
theorem comp {T : V →ₗ[ℝ] V'} {T' : V' →ₗ[ℝ] V''}
    (hT' : IsRationalLinearMap h' h'' T') (hT : IsRationalLinearMap h h' T) :
    IsRationalLinearMap h h'' (T'.comp T) := by
  intro f hf
  exact hT (f.comp T') (hT' f hf)

/-- Integral compatibility implies rationality. -/
theorem of_integral_compatible (h : IsIntegralLattice i) (h' : IsIntegralLattice i')
    (u : N →+ N') (T : V →ₗ[ℝ] V') (hT : ∀ n, T (i n) = i' (u n)) :
    IsRationalLinearMap h h' T :=
  fun _ hf => hf.comp h u T hT

/-- Every canonically extended integral map is rational. -/
theorem extend (h : IsIntegralLattice i) (h' : IsIntegralLattice i') (u : N →+ N') :
    IsRationalLinearMap h h' (h.extend i' u) :=
  of_integral_compatible h h' u (h.extend i' u) (fun n => h.extend_apply i' u n)

/-- The first projection from a product lattice is rational. -/
theorem fst (h : IsIntegralLattice i) (h' : IsIntegralLattice i') :
    IsRationalLinearMap (h.prod h') h (LinearMap.fst ℝ V V') :=
  of_integral_compatible _ _ (AddMonoidHom.fst N N') _ (fun _ => rfl)

/-- The second projection from a product lattice is rational. -/
theorem snd (h : IsIntegralLattice i) (h' : IsIntegralLattice i') :
    IsRationalLinearMap (h.prod h') h' (LinearMap.snd ℝ V V') :=
  of_integral_compatible _ _ (AddMonoidHom.snd N N') _ (fun _ => rfl)

end IsRationalLinearMap

end TauCeti.Toric
