/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Cycles and homology of homological complexes of modules

For a homological complex `K` of modules over a ring, the inclusion of the degree-`n` cycles into
`K.X n` is injective and the class map from the cycles onto the degree-`n` homology is surjective.
These are the elementwise forms of the facts that `K.iCycles n` is a monomorphism and
`K.homologyπ n` is an epimorphism.  Conversely, an element of `K.X n` killed by the differential
is a cycle, `HomologicalComplex.moduleCatCyclesMk`.  This constructor directly returns
an element of `K.cycles n` for modules over a ring in any universe, whereas Mathlib's
`HomologicalComplex.cyclesMk` returns an element of `(forget₂ C Ab).obj (K.cycles n)`.

For a cochain complex `K`, `K.cyclesShortComplex n` is the sequence
`Zⁿ(K) ⟶ Kⁿ ⟶ Zⁿ⁺¹(K)`. It is short exact whenever `K` is exact in degree `n + 1`.
-/

public section

open CategoryTheory

universe u

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) (n : ι)

/-- The inclusion of the degree-`n` cycles of a homological complex of modules into its degree-`n`
term is injective. -/
lemma moduleCat_iCycles_injective : Function.Injective (K.iCycles n) :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- The class map from the degree-`n` cycles of a homological complex of modules onto its
degree-`n` homology is surjective. -/
lemma moduleCat_homologyπ_surjective : Function.Surjective (K.homologyπ n) :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

variable {n} in
/-- An element `x` of `K.X n` killed by the differential `K.d n m` out of degree `n`, as a cycle
of degree `n`. -/
noncomputable def moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.cycles n :=
  (K.sc n).moduleCatCyclesIso.inv ⟨x, by subst hm; exact hx⟩

/-- The cycle `K.moduleCatCyclesMk x m hm hx` has underlying element `x`. -/
@[simp]
lemma iCycles_moduleCatCyclesMk (x : K.X n) (m : ι) (hm : c.next n = m)
    (hx : K.d n m x = 0) : K.iCycles n (K.moduleCatCyclesMk x m hm hx) = x :=
  (K.sc n).moduleCatCyclesIso_inv_iCycles_apply _

end HomologicalComplex

namespace HomologicalComplex

variable {R : Type*} [Ring R]

/-- The short complex `Zⁿ(K) ⟶ Kⁿ ⟶ Zⁿ⁺¹(K)` cut out of a cochain complex of modules. Its
second map is the differential with codomain restricted to the cycles in the next degree. -/
noncomputable def cyclesShortComplex
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    rw [← cancel_mono (K.iCycles (n + 1))]
    simp)

@[simp]
theorem cyclesShortComplex_X₁ (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (K.cyclesShortComplex n).X₁ = K.cycles n := by
  rw [cyclesShortComplex]

@[simp]
theorem cyclesShortComplex_X₂ (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (K.cyclesShortComplex n).X₂ = K.X n := by
  rw [cyclesShortComplex]

@[simp]
theorem cyclesShortComplex_X₃ (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (K.cyclesShortComplex n).X₃ = K.cycles (n + 1) := by
  rw [cyclesShortComplex]

/-- The first map of `K.cyclesShortComplex n` is the inclusion of the cycles, transported along
the object equalities `cyclesShortComplex_X₁` and `cyclesShortComplex_X₂`. -/
@[simp]
theorem cyclesShortComplex_f (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (K.cyclesShortComplex n).f = eqToHom (K.cyclesShortComplex_X₁ n) ≫ K.iCycles n ≫
      eqToHom (K.cyclesShortComplex_X₂ n).symm := by
  simp [cyclesShortComplex]
  -- The remaining `eqToHom` is along an equation whose two sides agree after unfolding.
  rfl

/-- The second map of `K.cyclesShortComplex n` is the differential corestricted to the cycles,
transported along the object equalities `cyclesShortComplex_X₂` and `cyclesShortComplex_X₃`. -/
@[simp]
theorem cyclesShortComplex_g (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (K.cyclesShortComplex n).g = eqToHom (K.cyclesShortComplex_X₂ n) ≫ K.toCycles n (n + 1) ≫
      eqToHom (K.cyclesShortComplex_X₃ n).symm := by
  simp [cyclesShortComplex]
  -- The remaining `eqToHom` is along an equation whose two sides agree after unfolding.
  rfl

/-- The cycle sequence `Zⁿ(K) ⟶ Kⁿ ⟶ Zⁿ⁺¹(K)` is short exact when `K` is exact in degree
`n + 1`. -/
theorem cyclesShortComplex_shortExact {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (n : ℤ) (hK : K.ExactAt (n + 1)) : (K.cyclesShortComplex n).ShortExact := by
  -- Expose the structure maps so typeclass search sees their canonical forms.
  have hf : Mono (K.cyclesShortComplex n).f := by
    change Mono (K.iCycles n)
    infer_instance
  have hg : Epi (K.cyclesShortComplex n).g := by
    change Epi (K.toCycles n (n + 1))
    have h := (ShortComplex.exact_iff_epi_toCycles (K.sc (n + 1))).mp hK
    -- Mathlib's exactness API indexes the source by `prev`; normalize it to `n`.
    change Epi (K.toCycles ((ComplexShape.up ℤ).prev (n + 1)) (n + 1)) at h
    have hn : (ComplexShape.up ℤ).prev (n + 1) = n := by simp
    rw [hn] at h
    exact h
  refine ShortComplex.ShortExact.mk' ?_ hf hg
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  -- Work with the concrete map recorded in the short complex.
  change K.toCycles n (n + 1) x = 0 at hx
  have hdx : K.d n (n + 1) x = 0 := by
    have h := congrArg (fun f : K.X n ⟶ K.X (n + 1) ↦ f x)
      (K.toCycles_i (i := n) (j := n + 1))
    -- Unfold composition only at this elementwise boundary.
    change K.iCycles (n + 1) (K.toCycles n (n + 1) x) = K.d n (n + 1) x at h
    rw [← h, hx, map_zero]
  exact ⟨K.moduleCatCyclesMk (n := n) x (n + 1) (by simp) hdx,
    K.iCycles_moduleCatCyclesMk n x (n + 1) (by simp) hdx⟩

end HomologicalComplex
