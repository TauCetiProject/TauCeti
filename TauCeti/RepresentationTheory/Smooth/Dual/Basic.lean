/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The smooth dual of a representation

Let `G` be a topological group and `ρ` a representation of `G` on an `A`-module `V`, where `A` is
a commutative semiring. The *smooth dual* (smooth contragredient) `V^∨` is the subrepresentation of
smooth vectors of the algebraic dual representation `Representation.dual ρ` on `Hom_A(V, A)`, in
which `g` acts by `λ ↦ λ ∘ ρ(g⁻¹)`. For a locally profinite group, its elements are the linear
forms fixed by some compact open subgroup.

For smooth `V` and `W`, an intertwining map `V → W^∨` is the same as an intertwining map
`V → W^*`, hence (swapping arguments, `Representation.dualHomEquiv`) the same as a `G`-invariant
bilinear pairing `V × W → A` and as an intertwining map `W → V^∨`. Applied to the identity of
`V^∨`, this gives the evaluation map `V → V^∨∨`.

## Main definitions

* `Representation.smoothDual ρ`: the smooth dual `V^∨`, the smooth vectors of `ρ.dual`.
* `Representation.IntertwiningMap.smoothDualMap f`: for `f : V → W`, the transpose `W^∨ → V^∨`.
* `Representation.intertwiningMapSmoothDualEquiv`: for smooth `V`, intertwining maps `V → W^∨` are
  the intertwining maps `V → W^*`.
* `Representation.smoothDualHomEquiv`: for smooth `V` and `W`, `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)`.
* `Representation.smoothDualEval ρ`: for smooth `V`, the evaluation map `V → V^∨∨`.

## Main results

* `Representation.smoothVectors_dual_eq_top_of_le_stabilizer`: if an open subgroup fixes every
  vector, every linear form is smooth.
* `Representation.smoothVectors_dual_eq_top`: the dual of a finitely generated smooth
  representation is smooth.
* `Representation.smoothDualHomEquiv_comp`, `Representation.smoothDualHomEquiv_smoothDualMap_comp`:
  naturality of `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)` in `V` and in `W`.
* `Representation.smoothDualEval_surjective_iff`: over a field, if an open subgroup fixes every
  vector, the evaluation map `V → V^∨∨` is surjective exactly when `V` is finite-dimensional.

## References

* J. Bernstein, *Representations of p-adic groups*, Harvard lectures 1992, written by
  K. Rumelhart, Chapter I, §2.2, Definition 8, p. 14.
* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, §2.8, p. 23.
-/

public section

open Module

namespace Representation

variable {A G V W : Type*} [CommSemiring A] [Group G]
  [AddCommMonoid V] [Module A V] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G V} {σ : Representation A G W}

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-! ### The smooth dual -/

section SmoothDual

variable (ρ) in
/-- The *smooth dual* (smooth contragredient) `V^∨` of a representation: the subrepresentation of
smooth vectors of the dual representation `ρ.dual` on `Hom_A(V, A)`, in which `g` acts by
`λ ↦ λ ∘ ρ(g⁻¹)`. -/
abbrev smoothDual : Representation A G ρ.dual.smoothVectors.toSubmodule :=
  ρ.dual.smoothVectors.toRepresentation

theorem smoothDual_apply_coe (g : G) (f : ρ.dual.smoothVectors.toSubmodule) (v : V) :
    (ρ.smoothDual g f : Dual A V) v = (f : Dual A V) (ρ g⁻¹ v) :=
  (rfl)

/-- If an open subgroup `U` fixes every vector, it fixes every linear form, and every linear form
is smooth. -/
theorem smoothVectors_dual_eq_top_of_le_stabilizer {U : Subgroup G} (hU : IsOpen (U : Set G))
    (h : ∀ v, U ≤ ρ.stabilizer v) : ρ.dual.smoothVectors = ⊤ :=
  eq_top_iff.2 fun f _ ↦ mem_smoothVectors_iff.2 (Subgroup.isOpen_mono (le_stabilizer_dual h f) hU)

/-- **The dual of a finitely generated smooth representation is smooth**: the stabilizers of
finitely many generators meet in an open subgroup fixing every vector. -/
theorem smoothVectors_dual_eq_top [IsSmooth ρ] [Module.Finite A V] :
    ρ.dual.smoothVectors = ⊤ := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := V)
  refine smoothVectors_dual_eq_top_of_le_stabilizer
    (U := ⨅ v ∈ (s : Set V), ρ.stabilizer v) ?_ fun v ↦ ?_
  · simp only [Subgroup.coe_iInf]
    exact s.finite_toSet.isOpen_biInter fun v _ ↦ IsSmooth.isOpen_stabilizer v
  · have hv : v ∈ Submodule.span A (s : Set V) := hs ▸ Submodule.mem_top
    rw [← biInf_stabilizer_span (R := A)]
    exact iInf₂_le v hv

/-- The smooth dual of a trivial representation is its whole dual. -/
theorem smoothVectors_dual_eq_top_of_isTrivial [ρ.IsTrivial] : ρ.dual.smoothVectors = ⊤ :=
  smoothVectors_dual_eq_top_of_le_stabilizer (U := ⊤) isOpen_univ fun v g _ ↦
    mem_stabilizer.2 (LinearMap.congr_fun (IsTrivial.out (ρ := ρ) g) v)

/-- The smooth dual of a representation on a module with at most one vector has at most one
vector. -/
instance [Subsingleton V] : Subsingleton ρ.dual.smoothVectors.toSubmodule :=
  ⟨fun f f' ↦ Subtype.ext (LinearMap.ext fun v ↦ by simp [Subsingleton.elim v 0])⟩

end SmoothDual

/-! ### Transpose of an intertwining map -/

section SmoothDualMap

variable {U : Type*} [AddCommMonoid U] [Module A U] {τ : Representation A G U}

/-- The transpose of an intertwining map `f : V → W` sends smooth linear forms on `W` to smooth
linear forms on `V`. -/
theorem IntertwiningMap.dualMap_mem_smoothVectors (f : IntertwiningMap ρ σ) {l : Dual A W}
    (hl : l ∈ σ.dual.smoothVectors) : f.dualMap l ∈ ρ.dual.smoothVectors :=
  f.dualMap.apply_mem_smoothVectors hl

/-- The transpose `W^∨ → V^∨` of an intertwining map `f : V → W`, `λ ↦ λ ∘ f`. -/
def IntertwiningMap.smoothDualMap (f : IntertwiningMap ρ σ) :
    IntertwiningMap σ.smoothDual ρ.smoothDual :=
  (f.dualMap.comp σ.dual.smoothVectors.subtype).codRestrict ρ.dual.smoothVectors fun l ↦ by
    simpa using f.dualMap_mem_smoothVectors l.property

@[simp]
theorem IntertwiningMap.smoothDualMap_apply_coe (f : IntertwiningMap ρ σ)
    (l : σ.dual.smoothVectors.toSubmodule) (v : V) :
    (f.smoothDualMap l : Dual A V) v = (l : Dual A W) (f v) := by
  simp [smoothDualMap]

@[simp]
theorem IntertwiningMap.smoothDualMap_id :
    (IntertwiningMap.id ρ).smoothDualMap = IntertwiningMap.id ρ.smoothDual :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

@[simp]
theorem IntertwiningMap.smoothDualMap_comp (f : IntertwiningMap ρ σ) (f' : IntertwiningMap σ τ) :
    (f'.comp f).smoothDualMap = f.smoothDualMap.comp f'.smoothDualMap :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

end SmoothDualMap

/-! ### Duality for intertwining maps -/

section Hom

/-- For smooth `V`, an intertwining map `V → W^∨` is the same as an intertwining map `V → W^*`:
the image of a smooth vector is smooth. -/
def intertwiningMapSmoothDualEquiv [IsSmooth ρ] :
    IntertwiningMap ρ σ.smoothDual ≃ₗ[A] IntertwiningMap ρ σ.dual where
  toFun f := σ.dual.smoothVectors.subtype.comp f
  invFun f := f.codRestrict σ.dual.smoothVectors fun v ↦
    f.apply_mem_smoothVectors (IsSmooth.mem_smoothVectors v)
  map_add' _ _ := IntertwiningMap.ext <| LinearMap.ext fun _ ↦ by simp
  map_smul' _ _ := IntertwiningMap.ext <| LinearMap.ext fun _ ↦ by simp
  left_inv _ := IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext (by simp)
  right_inv _ := IntertwiningMap.ext <| LinearMap.ext fun _ ↦ by simp

@[simp]
theorem intertwiningMapSmoothDualEquiv_apply [IsSmooth ρ] (f : IntertwiningMap ρ σ.smoothDual)
    (v : V) : intertwiningMapSmoothDualEquiv f v = f v := by
  simp [intertwiningMapSmoothDualEquiv]

@[simp]
theorem intertwiningMapSmoothDualEquiv_symm_apply_coe [IsSmooth ρ] (f : IntertwiningMap ρ σ.dual)
    (v : V) : (intertwiningMapSmoothDualEquiv.symm f v : Dual A W) = f v := by
  simp [intertwiningMapSmoothDualEquiv]

variable (ρ σ) in
/-- **Duality for intertwining maps into smooth duals.** For smooth representations `V` and `W`,
`Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)`, both sides being the `G`-invariant bilinear pairings `V × W → A`:
`f` corresponds to `w ↦ (v ↦ f v w)`. -/
def smoothDualHomEquiv [IsSmooth ρ] [IsSmooth σ] :
    IntertwiningMap ρ σ.smoothDual ≃ₗ[A] IntertwiningMap σ ρ.smoothDual :=
  intertwiningMapSmoothDualEquiv ≪≫ₗ dualHomEquiv ρ σ ≪≫ₗ intertwiningMapSmoothDualEquiv.symm

@[simp]
theorem smoothDualHomEquiv_apply_coe [IsSmooth ρ] [IsSmooth σ]
    (f : IntertwiningMap ρ σ.smoothDual) (w : W) (v : V) :
    (smoothDualHomEquiv ρ σ f w : Dual A V) v = (f v : Dual A W) w := by
  simp [smoothDualHomEquiv]

@[simp]
theorem smoothDualHomEquiv_symm [IsSmooth ρ] [IsSmooth σ] :
    (smoothDualHomEquiv ρ σ).symm = smoothDualHomEquiv σ ρ :=
  LinearEquiv.ext fun _ ↦ by simp [smoothDualHomEquiv]

/-- Naturality of `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)` in `V`. -/
theorem smoothDualHomEquiv_comp {V' : Type*} [AddCommMonoid V'] [Module A V']
    {ρ' : Representation A G V'} [IsSmooth ρ] [IsSmooth ρ'] [IsSmooth σ]
    (f : IntertwiningMap ρ σ.smoothDual) (u : IntertwiningMap ρ' ρ) :
    smoothDualHomEquiv ρ' σ (f.comp u) = u.smoothDualMap.comp (smoothDualHomEquiv ρ σ f) :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

/-- Naturality of `Hom_G(V, W^∨) ≃ Hom_G(W, V^∨)` in `W`. -/
theorem smoothDualHomEquiv_smoothDualMap_comp {W' : Type*} [AddCommMonoid W'] [Module A W']
    {σ' : Representation A G W'} [IsSmooth ρ] [IsSmooth σ] [IsSmooth σ']
    (f : IntertwiningMap ρ σ.smoothDual) (t : IntertwiningMap σ' σ) :
    smoothDualHomEquiv ρ σ' (t.smoothDualMap.comp f) = (smoothDualHomEquiv ρ σ f).comp t :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

end Hom

/-! ### Evaluation into the double smooth dual -/

section Eval

variable (ρ) in
/-- The evaluation map `V → V^∨∨`, `v ↦ (λ ↦ λ v)`, for a smooth representation `V`. It
corresponds to the identity of `V^∨` under `Hom_G(V^∨, V^∨) ≃ Hom_G(V, V^∨∨)`. -/
def smoothDualEval [IsSmooth ρ] : IntertwiningMap ρ ρ.smoothDual.smoothDual :=
  smoothDualHomEquiv ρ.smoothDual ρ (IntertwiningMap.id _)

@[simp]
theorem smoothDualEval_apply_coe [IsSmooth ρ] (v : V) (f : ρ.dual.smoothVectors.toSubmodule) :
    (ρ.smoothDualEval v : Dual A _) f = (f : Dual A V) v := by
  simp [smoothDualEval]

/-- **The evaluation map to the double smooth dual is natural.** -/
theorem smoothDualEval_comp [IsSmooth ρ] [IsSmooth σ] (f : IntertwiningMap ρ σ) :
    σ.smoothDualEval.comp f = f.smoothDualMap.smoothDualMap.comp ρ.smoothDualEval :=
  IntertwiningMap.ext <| LinearMap.ext fun _ ↦ Subtype.ext <| LinearMap.ext fun _ ↦ by simp

end Eval

/-! ### Surjectivity of the evaluation map -/

section Field

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- **The evaluation map is not surjective in infinite dimension.** Over a field, if an open
subgroup fixes every vector of `V`, then every linear form on `V` and on `V^∨` is smooth, and the
evaluation map `V → V^∨∨` is surjective exactly when `V` is finite-dimensional. -/
theorem smoothDualEval_surjective_iff [IsSmooth ρ] {U : Subgroup G} (hU : IsOpen (U : Set G))
    (h : ∀ v, U ≤ ρ.stabilizer v) :
    Function.Surjective ρ.smoothDualEval ↔ FiniteDimensional k V := by
  have h₁ := smoothVectors_dual_eq_top_of_le_stabilizer hU h
  have hfix (f : ρ.dual.smoothVectors.toSubmodule) : U ≤ ρ.smoothDual.stabilizer f := by
    rw [Subrepresentation.stabilizer_toRepresentation]
    exact le_stabilizer_dual h f
  have h₂ := smoothVectors_dual_eq_top_of_le_stabilizer hU hfix
  let e₁ := LinearEquiv.ofTop _ (congrArg Subrepresentation.toSubmodule h₁)
  let Φ := (LinearEquiv.ofTop _ (congrArg Subrepresentation.toSubmodule h₂)).trans
    e₁.symm.dualMap
  have hΦ : ⇑Φ ∘ ⇑ρ.smoothDualEval = Dual.eval k V := by
    ext v f
    simp [Φ, e₁, LinearEquiv.ofTop_apply]
  have key : Function.Surjective ρ.smoothDualEval ↔ Function.Surjective (Dual.eval k V) := by
    rw [← hΦ]
    exact (Φ.toEquiv.comp_surjective _).symm
  rw [key]
  refine ⟨fun hs ↦ ?_, fun _ ↦ (bijective_dual_eval k V).2⟩
  have : IsReflexive k V := ⟨⟨eval_apply_injective k, hs⟩⟩
  exact instFiniteDimensionalOfIsReflexive k V

end Field

end Representation
