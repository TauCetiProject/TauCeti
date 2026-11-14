/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Geometry.Manifold.MFDeriv.Pi

/-!
# Simplicial structure of iterated submersion fibre products

For a map `π : Y → M`, contravariant reindexing along any map `α : Fin k₁ → Fin k₂` defines a map
`TauCeti.IteratedFiberProduct.reindex α : IteratedFiberProduct π k₂ → IteratedFiberProduct π k₁`
sending `(y₀, …, y_{k₂ - 1})` to `(y_{α 0}, …, y_{α (k₁ - 1)})`. Specializing `α` to the standard
coface and codegeneracy maps `Fin.succAbove` and `Fin.predAbove` gives the Čech nerve of `π`:

* `TauCeti.IteratedFiberProduct.face i : Y^[m + 2] → Y^[m + 1]`, omitting the `i`-th factor; for
  `m = 0`, `face 0` and `face 1` recover the second and first projections `Y^[2] → Y^[1]`, so the
  alternating pullback differential `∑ᵢ (-1)ⁱ (face i)*` on `Y^[2]` is `pr₂* - pr₁*`;
* `TauCeti.IteratedFiberProduct.degeneracy i : Y^[m + 1] → Y^[m + 2]`, repeating the `i`-th factor
  along the corresponding partial diagonal;
* all five simplicial identities (`face_comp_face`,
  `face_castSucc_comp_degeneracy_succ_of_le`, `face_castSucc_comp_degeneracy` and
  `face_succ_comp_degeneracy`, `face_succ_comp_degeneracy_castSucc_of_gt`, and
  `degeneracy_castSucc_comp_degeneracy`), transferred from `SimplexCategory` via contravariant
  functoriality `reindex (β ∘ α) = reindex α ∘ reindex β`.

When `π` is a `C^n` submersion (`1 ≤ n`) between finite-dimensional boundaryless real manifolds and
each `IteratedFiberProduct π (m + 1)` carries `TauCeti.iteratedFiberProductChartedSpace`:

* every reindexing map `reindex α` is `C^{m'}` (`m' ≤ n`), and a bijection `α : Fin k₁ ≃ Fin k₂`
  induces a `C^n` diffeomorphism (`TauCeti.iteratedFiberProductReindexDiffeomorph`);
* reindexing along any injective map `α : Fin (m₁ + 1) → Fin (m₂ + 1)` is a surjective `C^n`
  submersion (`TauCeti.isSubmersion_reindex_of_injective`); in particular, every face map `face i`
  is a surjective `C^n` submersion (`TauCeti.isSubmersion_face`,
  `TauCeti.IteratedFiberProduct.surjective_face`);
* every degeneracy map `degeneracy i` is a `C^n` smooth embedding (`TauCeti.contMDiff_degeneracy`,
  `TauCeti.isSmoothEmbedding_degeneracy`), and a closed topological embedding when `Y` is
  Hausdorff (`TauCeti.IteratedFiberProduct.isClosedEmbedding_degeneracy`).

## References

* J.-L. Brylinski, *Loop Spaces, Characteristic Classes and Geometric Quantization*,
  Progress in Mathematics 107, Birkhäuser (1993), Chapter V (smooth Čech nerves of submersions).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) **54** (1996), 403–416.
-/

public section

open Function Set Module Topology
open scoped Manifold ContDiff

namespace TauCeti

namespace IteratedFiberProduct

section Set

variable {Y M : Type*} {π : Y → M}

/-- Contravariant reindexing of `IteratedFiberProduct π` along `α : Fin k₁ → Fin k₂`, sending
`y` to `y ∘ α`. -/
def reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (y : IteratedFiberProduct π k₂) :
    IteratedFiberProduct π k₁ :=
  ⟨y.1 ∘ α, fun i j ↦ y.2 (α i) (α j)⟩

/-- The underlying tuple of `reindex α y` is `y.1 ∘ α`. -/
@[simp]
theorem coe_reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (y : IteratedFiberProduct π k₂) :
    (reindex α y : Fin k₁ → Y) = y.1 ∘ α := (rfl)

/-- Evaluating `reindex α y` at `i` evaluates `y` at `α i`. -/
theorem eval_reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (y : IteratedFiberProduct π k₂)
    (i : Fin k₁) :
    eval i (reindex α y) = eval (α i) y := by
  simp only [eval_apply, coe_reindex, comp_apply]

/-- Reindexing along the identity map is the identity on `IteratedFiberProduct π k`. -/
@[simp]
theorem reindex_id {k : ℕ} :
    (reindex (id : Fin k → Fin k) : IteratedFiberProduct π k → IteratedFiberProduct π k) = id :=
  (rfl)

/-- Pointwise form of `reindex_id`. -/
@[simp]
theorem reindex_id_apply {k : ℕ} (y : IteratedFiberProduct π k) :
    reindex id y = y := (rfl)

/-- Reindexing is contravariantly functorial: `reindex (β ∘ α) = reindex α ∘ reindex β`. -/
theorem reindex_comp {k₁ k₂ k₃ : ℕ} (α : Fin k₁ → Fin k₂) (β : Fin k₂ → Fin k₃) :
    (reindex (β ∘ α) : IteratedFiberProduct π k₃ → IteratedFiberProduct π k₁) =
      reindex α ∘ reindex β := (rfl)

/-- Pointwise form of `reindex_comp`. -/
@[simp]
theorem reindex_reindex {k₁ k₂ k₃ : ℕ} (α : Fin k₁ → Fin k₂) (β : Fin k₂ → Fin k₃)
    (y : IteratedFiberProduct π k₃) :
    reindex α (reindex β y) = reindex (β ∘ α) y := (rfl)

/-- Reindexing a constant diagonal tuple produces the constant diagonal tuple. -/
@[simp]
theorem reindex_const {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) (z : Y) :
    reindex α (const (π := π) k₂ z) = const k₁ z :=
  ext fun _ ↦ by simp only [eval_reindex, eval_const]

/-- Reindexing between positive arities preserves `baseProj`. -/
@[simp]
theorem baseProj_reindex {m₁ m₂ : ℕ} (α : Fin (m₁ + 1) → Fin (m₂ + 1))
    (y : IteratedFiberProduct π (m₂ + 1)) :
    baseProj (reindex α y) = baseProj y := by
  rw [baseProj_eq_apply _ 0, baseProj_eq_apply _ 0]
  exact (y.2 0 (α 0)).symm

/-- Reindexing along an injective map between nonempty index sets is surjective: unassigned
coordinates can be filled with coordinate `0` of the given tuple, which lies in the same fibre. -/
theorem surjective_reindex_of_injective {m₁ m₂ : ℕ} {α : Fin (m₁ + 1) → Fin (m₂ + 1)}
    (hα : Injective α) :
    Surjective (reindex (π := π) α) := by
  intro x
  let g : Fin (m₂ + 1) → Y := extend α x.1 (fun _ ↦ x.1 0)
  have hg_base : ∀ j : Fin (m₂ + 1), π (g j) = baseProj x := by
    intro j
    by_cases hj : ∃ i, α i = j
    · obtain ⟨i, rfl⟩ := hj
      change π (extend α x.1 (fun _ ↦ x.1 0) (α i)) = baseProj x
      rw [hα.extend_apply, baseProj_eq_apply x i]
    · change π (extend α x.1 (fun _ ↦ x.1 0) j) = baseProj x
      rw [extend_apply' _ _ _ hj, baseProj_eq_apply x 0]
  refine ⟨⟨g, fun j₁ j₂ ↦ (hg_base j₁).trans (hg_base j₂).symm⟩, ext fun i ↦ ?_⟩
  rw [eval_apply, eval_apply]
  exact hα.extend_apply x.1 (fun _ ↦ x.1 0) i

/-- Reindexing along a surjective map is injective. -/
theorem injective_reindex_of_surjective {k₁ k₂ : ℕ} {α : Fin k₁ → Fin k₂}
    (hα : Surjective α) :
    Injective (reindex (π := π) α) := by
  intro y₁ y₂ h
  refine ext fun j ↦ ?_
  obtain ⟨i, rfl⟩ := hα j
  simpa only [eval_reindex] using congrArg (eval i) h

/-- The `i`-th face map `Y^[m + 2] → Y^[m + 1]`, omitting coordinate `i` via `Fin.succAbove i`. -/
def face {m : ℕ} (i : Fin (m + 2)) :
    IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1) :=
  reindex i.succAbove

/-- `face i` is reindexing along `i.succAbove`. -/
theorem face_eq_reindex {m : ℕ} (i : Fin (m + 2)) :
    (face i : IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) =
      reindex i.succAbove := (rfl)

/-- The underlying tuple of `face i y` is `y.1 ∘ i.succAbove`. -/
@[simp]
theorem coe_face {m : ℕ} (i : Fin (m + 2)) (y : IteratedFiberProduct π (m + 2)) :
    (face i y : Fin (m + 1) → Y) = y.1 ∘ i.succAbove := (rfl)

/-- Evaluating `face i y` at `j` evaluates `y` at `i.succAbove j`. -/
theorem eval_face {m : ℕ} (i : Fin (m + 2)) (j : Fin (m + 1))
    (y : IteratedFiberProduct π (m + 2)) :
    eval j (face i y) = eval (i.succAbove j) y :=
  eval_reindex i.succAbove y j

/-- On `Y^[2]`, `face 0` omits coordinate `0` and therefore reads coordinate `1` (`pr₂`). -/
theorem eval_zero_face_zero (y : IteratedFiberProduct π 2) :
    eval 0 (face 0 y) = eval 1 y :=
  eval_face 0 0 y

/-- On `Y^[2]`, `face 1` omits coordinate `1` and therefore reads coordinate `0` (`pr₁`). -/
theorem eval_zero_face_one (y : IteratedFiberProduct π 2) :
    eval 0 (face 1 y) = eval 0 y :=
  eval_face 1 0 y

/-- Every face map sends a constant diagonal tuple to the constant diagonal tuple. -/
@[simp]
theorem face_const {m : ℕ} (i : Fin (m + 2)) (z : Y) :
    face i (const (π := π) (m + 2) z) = const (m + 1) z :=
  reindex_const i.succAbove z

/-- Every face map commutes with `baseProj`. -/
@[simp]
theorem baseProj_face {m : ℕ} (i : Fin (m + 2)) (y : IteratedFiberProduct π (m + 2)) :
    baseProj (face i y) = baseProj y :=
  baseProj_reindex i.succAbove y

/-- Every face map `face i : Y^[m + 2] → Y^[m + 1]` is surjective. -/
theorem surjective_face {m : ℕ} (i : Fin (m + 2)) :
    Surjective (face i : IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) :=
  surjective_reindex_of_injective Fin.succAbove_right_injective

/-- The `i`-th diagonal degeneracy map `Y^[m + 1] → Y^[m + 2]`, repeating coordinate `i` via
`Fin.predAbove i`. -/
def degeneracy {m : ℕ} (i : Fin (m + 1)) :
    IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2) :=
  reindex i.predAbove

/-- `degeneracy i` is reindexing along `i.predAbove`. -/
theorem degeneracy_eq_reindex {m : ℕ} (i : Fin (m + 1)) :
    (degeneracy i : IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) =
      reindex i.predAbove := (rfl)

/-- The underlying tuple of `degeneracy i y` is `y.1 ∘ i.predAbove`. -/
@[simp]
theorem coe_degeneracy {m : ℕ} (i : Fin (m + 1)) (y : IteratedFiberProduct π (m + 1)) :
    (degeneracy i y : Fin (m + 2) → Y) = y.1 ∘ i.predAbove := (rfl)

/-- Evaluating `degeneracy i y` at `j` evaluates `y` at `i.predAbove j`. -/
theorem eval_degeneracy {m : ℕ} (i : Fin (m + 1)) (j : Fin (m + 2))
    (y : IteratedFiberProduct π (m + 1)) :
    eval j (degeneracy i y) = eval (i.predAbove j) y :=
  eval_reindex i.predAbove y j

/-- Every degeneracy map sends a constant diagonal tuple to the constant diagonal tuple. -/
@[simp]
theorem degeneracy_const {m : ℕ} (i : Fin (m + 1)) (z : Y) :
    degeneracy i (const (π := π) (m + 1) z) = const (m + 2) z :=
  reindex_const i.predAbove z

/-- Every degeneracy map commutes with `baseProj`. -/
@[simp]
theorem baseProj_degeneracy {m : ℕ} (i : Fin (m + 1)) (y : IteratedFiberProduct π (m + 1)) :
    baseProj (degeneracy i y) = baseProj y :=
  baseProj_reindex i.predAbove y

/-! ### Simplicial identities -/

/-- **First simplicial identity**: for `i ≤ j`, `face i ∘ face j.succ = face j ∘ face i.castSucc`.
-/
theorem face_comp_face {m : ℕ} {i j : Fin (m + 2)} (hij : i ≤ j) :
    (face i ∘ face j.succ : IteratedFiberProduct π (m + 3) → IteratedFiberProduct π (m + 1)) =
      face j ∘ face i.castSucc := by
  have h : (j.succ.succAbove ∘ i.succAbove : Fin (m + 1) → Fin (m + 3)) =
      i.castSucc.succAbove ∘ j.succAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_δ hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the first simplicial identity. -/
theorem face_face_succ {m : ℕ} {i j : Fin (m + 2)} (hij : i ≤ j)
    (y : IteratedFiberProduct π (m + 3)) :
    face i (face j.succ y) = face j (face i.castSucc y) :=
  congrFun (face_comp_face hij) y

/-- Special case `i = j` of the first simplicial identity:
`face i ∘ face i.succ = face i ∘ face i.castSucc`. -/
theorem face_comp_face_self {m : ℕ} (i : Fin (m + 2)) :
    (face i ∘ face i.succ : IteratedFiberProduct π (m + 3) → IteratedFiberProduct π (m + 1)) =
      face i ∘ face i.castSucc :=
  face_comp_face le_rfl

/-- **Second simplicial identity**: for `i ≤ j.castSucc`,
`face i.castSucc ∘ degeneracy j.succ = degeneracy j ∘ face i`. -/
theorem face_castSucc_comp_degeneracy_succ_of_le {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : i ≤ j.castSucc) :
    (face i.castSucc ∘ degeneracy j.succ :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 2)) =
      degeneracy j ∘ face i := by
  have h : (j.succ.predAbove ∘ i.castSucc.succAbove : Fin (m + 2) → Fin (m + 2)) =
      i.succAbove ∘ j.predAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_le hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the second simplicial identity. -/
theorem face_castSucc_degeneracy_succ_of_le {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : i ≤ j.castSucc) (y : IteratedFiberProduct π (m + 2)) :
    face i.castSucc (degeneracy j.succ y) = degeneracy j (face i y) :=
  congrFun (face_castSucc_comp_degeneracy_succ_of_le hij) y

/-- **Third simplicial identity (first part)**: `face i.castSucc ∘ degeneracy i = id`. -/
theorem face_castSucc_comp_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    (face i.castSucc ∘ degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 1)) = id := by
  have h : (i.predAbove ∘ i.castSucc.succAbove : Fin (m + 1) → Fin (m + 1)) = id :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_self (i := i)))
  exact (reindex_comp _ _).symm.trans (congrArg reindex h)

/-- Pointwise form of `face_castSucc_comp_degeneracy`. -/
@[simp]
theorem face_castSucc_degeneracy {m : ℕ} (i : Fin (m + 1))
    (y : IteratedFiberProduct π (m + 1)) :
    face i.castSucc (degeneracy i y) = y :=
  congrFun (face_castSucc_comp_degeneracy i) y

/-- `face i.castSucc` is a left inverse to `degeneracy i`. -/
theorem leftInverse_face_castSucc_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    LeftInverse (face (π := π) i.castSucc) (degeneracy i) :=
  face_castSucc_degeneracy i

/-- **Third simplicial identity (second part)**: `face i.succ ∘ degeneracy i = id`. -/
theorem face_succ_comp_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    (face i.succ ∘ degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 1)) = id := by
  have h : (i.predAbove ∘ i.succ.succAbove : Fin (m + 1) → Fin (m + 1)) = id :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_succ (i := i)))
  exact (reindex_comp _ _).symm.trans (congrArg reindex h)

/-- Pointwise form of `face_succ_comp_degeneracy`. -/
@[simp]
theorem face_succ_degeneracy {m : ℕ} (i : Fin (m + 1))
    (y : IteratedFiberProduct π (m + 1)) :
    face i.succ (degeneracy i y) = y :=
  congrFun (face_succ_comp_degeneracy i) y

/-- `face i.succ` is a left inverse to `degeneracy i`. -/
theorem leftInverse_face_succ_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    LeftInverse (face (π := π) i.succ) (degeneracy i) :=
  face_succ_degeneracy i

/-- Every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is injective. -/
theorem injective_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    Injective (degeneracy i : IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) :=
  (leftInverse_face_castSucc_degeneracy i).injective

/-- **Fourth simplicial identity**: for `j.castSucc < i`,
`face i.succ ∘ degeneracy j.castSucc = degeneracy j ∘ face i`. -/
theorem face_succ_comp_degeneracy_castSucc_of_gt {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : j.castSucc < i) :
    (face i.succ ∘ degeneracy j.castSucc :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 2)) =
      degeneracy j ∘ face i := by
  have h : (j.castSucc.predAbove ∘ i.succ.succAbove : Fin (m + 2) → Fin (m + 2)) =
      i.succAbove ∘ j.predAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_gt hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the fourth simplicial identity. -/
theorem face_succ_degeneracy_castSucc_of_gt {m : ℕ} {i : Fin (m + 2)} {j : Fin (m + 1)}
    (hij : j.castSucc < i) (y : IteratedFiberProduct π (m + 2)) :
    face i.succ (degeneracy j.castSucc y) = degeneracy j (face i y) :=
  congrFun (face_succ_comp_degeneracy_castSucc_of_gt hij) y

/-- **Fifth simplicial identity**: for `i ≤ j`,
`degeneracy i.castSucc ∘ degeneracy j = degeneracy j.succ ∘ degeneracy i`. -/
theorem degeneracy_castSucc_comp_degeneracy {m : ℕ} {i j : Fin (m + 1)} (hij : i ≤ j) :
    (degeneracy i.castSucc ∘ degeneracy j :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 3)) =
      degeneracy j.succ ∘ degeneracy i := by
  have h : (j.predAbove ∘ i.castSucc.predAbove : Fin (m + 3) → Fin (m + 1)) =
      i.predAbove ∘ j.succ.predAbove :=
    funext (SimplexCategory.congr_toOrderHom_apply (SimplexCategory.σ_comp_σ hij))
  exact (reindex_comp _ _).symm.trans ((congrArg reindex h).trans (reindex_comp _ _))

/-- Pointwise form of the fifth simplicial identity. -/
theorem degeneracy_castSucc_degeneracy {m : ℕ} {i j : Fin (m + 1)} (hij : i ≤ j)
    (y : IteratedFiberProduct π (m + 1)) :
    degeneracy i.castSucc (degeneracy j y) = degeneracy j.succ (degeneracy i y) :=
  congrFun (degeneracy_castSucc_comp_degeneracy hij) y

end Set

section Topology

variable {Y M : Type*} [TopologicalSpace Y] {π : Y → M}

/-- Contravariant reindexing of `IteratedFiberProduct π` is continuous. -/
theorem continuous_reindex {k₁ k₂ : ℕ} (α : Fin k₁ → Fin k₂) :
    Continuous (reindex (π := π) α) :=
  Continuous.subtype_mk
    (continuous_pi fun i ↦ (continuous_eval (π := π) (α i)).congr fun a ↦ eval_apply (α i) a) _

/-- Every face map `face i : Y^[m + 2] → Y^[m + 1]` is continuous. -/
theorem continuous_face {m : ℕ} (i : Fin (m + 2)) :
    Continuous (face (π := π) i) :=
  continuous_reindex i.succAbove

/-- Every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is continuous. -/
theorem continuous_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    Continuous (degeneracy (π := π) i) :=
  continuous_reindex i.predAbove

/-- Every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is a topological embedding, split
by `face i.castSucc`. -/
theorem isEmbedding_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    IsEmbedding (degeneracy (π := π) i) :=
  (leftInverse_face_castSucc_degeneracy i).isEmbedding
    (continuous_face i.castSucc) (continuous_degeneracy i)

/-- When `Y` is Hausdorff, every degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is a closed
topological embedding. -/
theorem isClosedEmbedding_degeneracy [T2Space Y] {m : ℕ} (i : Fin (m + 1)) :
    IsClosedEmbedding (degeneracy (π := π) i) :=
  (leftInverse_face_castSucc_degeneracy i).isClosedEmbedding
    (continuous_face i.castSucc) (continuous_degeneracy i)

end Topology

end IteratedFiberProduct

section Manifold

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω}
  [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  {π : Y → M} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- Contravariant reindexing `reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_reindex {m₁ m₂ : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n)
    (α : Fin (m₁ + 1) → Fin (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    ContMDiff
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → IteratedFiberProduct π (m₁ + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m₂
  let := iteratedFiberProductChartedSpace hn hπ m₁
  refine (contMDiff_iteratedFiberProduct_iff hn hπ hm').2 fun i ↦ ?_
  simp only [IteratedFiberProduct.eval_reindex]
  exact contMDiff_eval hn hπ hm' (α i)

/-- Reindexing along an equivalence `α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)` induces a `C^n`
diffeomorphism `Y^[m₂ + 1] ≃ₘ^n Y^[m₁ + 1]`. In particular, permuting the factors of `Y^[k]` is a
`C^n` diffeomorphism. -/
noncomputable def iteratedFiberProductReindexDiffeomorph {m₁ m₂ : ℕ}
    (α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    IteratedFiberProduct π (m₂ + 1) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ)⟯
      IteratedFiberProduct π (m₁ + 1) := by
  letI := iteratedFiberProductChartedSpace hn hπ m₂
  letI := iteratedFiberProductChartedSpace hn hπ m₁
  exact
    { toFun := IteratedFiberProduct.reindex α
      invFun := IteratedFiberProduct.reindex α.symm
      left_inv := fun y ↦ IteratedFiberProduct.ext fun j ↦ by simp
      right_inv := fun x ↦ IteratedFiberProduct.ext fun i ↦ by simp
      contMDiff_toFun := contMDiff_reindex hn hπ le_rfl α
      contMDiff_invFun := contMDiff_reindex hn hπ le_rfl α.symm }

/-- `iteratedFiberProductReindexDiffeomorph` acts by `IteratedFiberProduct.reindex α`. -/
@[simp]
theorem iteratedFiberProductReindexDiffeomorph_apply {m₁ m₂ : ℕ}
    (α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)) (y : IteratedFiberProduct π (m₂ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    iteratedFiberProductReindexDiffeomorph hn hπ α y = IteratedFiberProduct.reindex α y := (rfl)

/-- The inverse of `iteratedFiberProductReindexDiffeomorph` acts by
`IteratedFiberProduct.reindex α.symm`. -/
@[simp]
theorem iteratedFiberProductReindexDiffeomorph_symm_apply {m₁ m₂ : ℕ}
    (α : Fin (m₁ + 1) ≃ Fin (m₂ + 1)) (x : IteratedFiberProduct π (m₁ + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    (iteratedFiberProductReindexDiffeomorph hn hπ α).symm x =
      IteratedFiberProduct.reindex α.symm x := (rfl)

/-- **Reindexing along an injective map is a submersion.** For any injective map
`α : Fin (m₁ + 1) → Fin (m₂ + 1)`, `reindex α : Y^[m₂ + 1] → Y^[m₁ + 1]` is a `C^n` submersion. -/
theorem isSubmersion_reindex_of_injective {m₁ m₂ : ℕ} {α : Fin (m₁ + 1) → Fin (m₂ + 1)}
    (hα : Injective α) :
    letI := iteratedFiberProductChartedSpace hn hπ m₂
    letI := iteratedFiberProductChartedSpace hn hπ m₁
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m₂ + 1) * finrank ℝ EY - m₂ * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → IteratedFiberProduct π (m₁ + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ m₂
  let := iteratedFiberProductChartedSpace hn hπ m₁
  have := isManifold_iteratedFiberProduct hn hπ m₂
  have := isManifold_iteratedFiberProduct hn hπ m₁
  let K₁ := 𝓘(ℝ, Fin ((m₁ + 1) * finrank ℝ EY - m₁ * finrank ℝ EM) → ℝ)
  let PI₁ := ModelWithCorners.pi fun _ : Fin (m₁ + 1) ↦ IY
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  refine ((contMDiff_reindex hn hπ le_rfl α).isSubmersionOfComplement_of_surjective_mfderiv hn
    fun y η ↦ ?_).isSubmersion
  let x : IteratedFiberProduct π (m₁ + 1) := IteratedFiberProduct.reindex α y
  let u := mfderiv K₁ PI₁ Subtype.val x η
  have hu : ∀ i₁ i₂ : Fin (m₁ + 1),
      mfderiv IY IM π (y.1 (α i₁)) (u i₁) =
        tangentSpaceCast IM (π (y.1 (α i₂))) (π (y.1 (α i₁)))
          (mfderiv IY IM π (y.1 (α i₂)) (u i₂)) :=
    (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m₁ x u).1 ⟨η, rfl⟩
  let w₀ : TangentSpace IM (π (y.1 (α 0))) := mfderiv IY IM π (y.1 (α 0)) (u 0)
  have hsurj : ∀ j : Fin (m₂ + 1),
      ∃ v_j : TangentSpace IY (y.1 j),
        (∀ i : Fin (m₁ + 1), α i = j →
          tangentSpaceCast IY (y.1 j) (y.1 (α i)) v_j = u i) ∧
        tangentSpaceCast IM (π (y.1 j)) (π (y.1 (α 0))) (mfderiv IY IM π (y.1 j) v_j) = w₀ := by
    intro j
    by_cases hj : ∃ i, α i = j
    · obtain ⟨i₀, rfl⟩ := hj
      refine ⟨u i₀, fun i hi ↦ ?_, (hu 0 i₀).symm⟩
      cases hα hi
      rfl
    · obtain ⟨v_j, hv_j⟩ :=
        ((tangentSpaceCast IM (π (y.1 j)) (π (y.1 (α 0)))).surjective.comp
          (hπ.surjective_mfderiv hn0 (y.1 j))) w₀
      exact ⟨v_j, fun i hi ↦ (hj ⟨i, hi⟩).elim, hv_j⟩
  choose v hv_hit hv_map using hsurj
  have hcompat : ∀ j₁ j₂ : Fin (m₂ + 1),
      mfderiv IY IM π (y.1 j₁) (v j₁) =
        tangentSpaceCast IM (π (y.1 j₂)) (π (y.1 j₁)) (mfderiv IY IM π (y.1 j₂) (v j₂)) := by
    intro j₁ j₂
    have hcast : ∀ {a b c : M}, a = b → b = c → ∀ (z : TangentSpace IM a),
        tangentSpaceCast IM b c (tangentSpaceCast IM a b z) = tangentSpaceCast IM a c z := by
      rintro _ _ _ rfl rfl _
      rfl
    have hself : ∀ {a : M} (z : TangentSpace IM a), tangentSpaceCast IM a a z = z :=
      fun _ ↦ rfl
    calc mfderiv IY IM π (y.1 j₁) (v j₁)
        = tangentSpaceCast IM (π (y.1 (α 0))) (π (y.1 j₁))
            (tangentSpaceCast IM (π (y.1 j₁)) (π (y.1 (α 0)))
              (mfderiv IY IM π (y.1 j₁) (v j₁))) := by
          rw [hcast (y.2 j₁ (α 0)) (y.2 (α 0) j₁), hself]
      _ = tangentSpaceCast IM (π (y.1 (α 0))) (π (y.1 j₁))
            (tangentSpaceCast IM (π (y.1 j₂)) (π (y.1 (α 0)))
              (mfderiv IY IM π (y.1 j₂) (v j₂))) := by
          rw [hv_map j₁, hv_map j₂]
      _ = tangentSpaceCast IM (π (y.1 j₂)) (π (y.1 j₁)) (mfderiv IY IM π (y.1 j₂) (v j₂)) :=
          hcast (y.2 j₂ (α 0)) (y.2 (α 0) j₁) _
  have hemb₁ := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m₁
  have hemb₂ := isSmoothEmbedding_coe_iteratedFiberProduct hn hπ m₂
  obtain ⟨ξ, hξ⟩ := (mem_range_mfderiv_coe_iteratedFiberProduct_iff hn hπ m₂ y v).2 hcompat
  refine ⟨ξ, (hemb₁.isImmersion.isImmersionAt x).mfderiv_injective hn0 ?_⟩
  have hc_lhs := mfderiv_comp y ((hemb₁.contMDiff x).mdifferentiableAt hn0)
    (((contMDiff_reindex hn hπ le_rfl α) y).mdifferentiableAt hn0)
  rw [← ContinuousLinearMap.comp_apply, ← hc_lhs]
  funext i
  have hc₁ := mfderiv_comp y (TauCeti.hasMFDerivAt_apply i x.1).mdifferentiableAt
    (((hemb₁.contMDiff.comp (contMDiff_reindex hn hπ le_rfl α)) y).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply] at hc₁
  have hfn : ((fun f : Fin (m₁ + 1) → Y ↦ f i) ∘
      (Subtype.val ∘ IteratedFiberProduct.reindex α :
        IteratedFiberProduct π (m₂ + 1) → (Fin (m₁ + 1) → Y))) =
      (fun g : Fin (m₂ + 1) → Y ↦ g (α i)) ∘ Subtype.val := rfl
  have hc₂ := mfderiv_comp y (TauCeti.hasMFDerivAt_apply (α i) y.1).mdifferentiableAt
    ((hemb₂.contMDiff y).mdifferentiableAt hn0)
  rw [TauCeti.mfderiv_apply] at hc₂
  have hlhs := (DFunLike.congr_fun hc₁ ξ).symm
  rw [hfn, hc₂] at hlhs
  exact hlhs.trans ((congrFun hξ (α i)).trans (hv_hit (α i) i rfl))

/-- Every face map `face i : Y^[m + 2] → Y^[m + 1]` is `C^{m'}` for `m' ≤ n`. -/
theorem contMDiff_face {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) (i : Fin (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    ContMDiff
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.face i :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  let := iteratedFiberProductChartedSpace hn hπ m
  exact contMDiff_reindex hn hπ hm' i.succAbove

/-- **Every face map is a surjective submersion.** On `IteratedFiberProduct π (m + 2)`, each face
map `face i : Y^[m + 2] → Y^[m + 1]` omitting the `i`-th factor is a `C^n` submersion. -/
theorem isSubmersion_face {m : ℕ} (i : Fin (m + 2)) :
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    letI := iteratedFiberProductChartedSpace hn hπ m
    Manifold.IsSubmersion
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.face i :
        IteratedFiberProduct π (m + 2) → IteratedFiberProduct π (m + 1)) := by
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  let := iteratedFiberProductChartedSpace hn hπ m
  exact isSubmersion_reindex_of_injective hn hπ Fin.succAbove_right_injective

/-- Every diagonal degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is `C^{m'}` for
`m' ≤ n`. -/
theorem contMDiff_degeneracy {m : ℕ} {m' : ℕ∞ω} (hm' : m' ≤ n) (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    ContMDiff
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) m'
      (IteratedFiberProduct.degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  exact contMDiff_reindex hn hπ hm' i.predAbove

/-- Every diagonal degeneracy map `degeneracy i : Y^[m + 1] → Y^[m + 2]` is a `C^n` immersion,
split on the left by `face i.castSucc`. -/
theorem isImmersion_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    Manifold.IsImmersion
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  have := isManifold_iteratedFiberProduct hn hπ m
  have := isManifold_iteratedFiberProduct hn hπ (m + 1)
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  exact (contMDiff_degeneracy hn hπ le_rfl i).isImmersion_of_leftInverse hn
    (fun _ ↦ ((contMDiff_face hn hπ le_rfl i.castSucc) _).mdifferentiableAt hn0)
    (IteratedFiberProduct.leftInverse_face_castSucc_degeneracy i)

/-- **Every diagonal degeneracy map is a smooth embedding.** On `IteratedFiberProduct π (m + 1)`,
`degeneracy i : Y^[m + 1] → Y^[m + 2]` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_degeneracy {m : ℕ} (i : Fin (m + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ m
    letI := iteratedFiberProductChartedSpace hn hπ (m + 1)
    Manifold.IsSmoothEmbedding
      𝓘(ℝ, Fin ((m + 1) * finrank ℝ EY - m * finrank ℝ EM) → ℝ)
      𝓘(ℝ, Fin ((m + 2) * finrank ℝ EY - (m + 1) * finrank ℝ EM) → ℝ) n
      (IteratedFiberProduct.degeneracy i :
        IteratedFiberProduct π (m + 1) → IteratedFiberProduct π (m + 2)) := by
  let := iteratedFiberProductChartedSpace hn hπ m
  let := iteratedFiberProductChartedSpace hn hπ (m + 1)
  exact ⟨isImmersion_degeneracy hn hπ i, IteratedFiberProduct.isEmbedding_degeneracy i⟩

end Manifold

end TauCeti
