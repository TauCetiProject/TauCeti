/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projection
public import TauCeti.AlgebraicTopology.CubicalModule.Basic
import TauCeti.Algebra.Category.ModuleCat.OfHom

/-!
# The normalized complex of a cubical module

For a cubical module `A`, the **normalized** `n`-cubes are those all of whose faces at `∞`
vanish, `Nₙ = ⋂ᵢ ker ∂ᵢ^∞`, and the **degenerate** `n`-cubes form the span `Dₙ = ∑ᵢ im sᵢ` of
the images of the degeneracies. Both are subcomplexes of the cubical boundary complex, and on
`N` the boundary is `∑ᵢ (-1)ⁱ ∂ᵢ⁰`.

The elementary projectors `1 - sᵢ ∘ ∂ᵢ^∞` kill the image of `sᵢ` and the `∞`-face in the `i`-th
coordinate, and they commute with the other faces and degeneracies up to reindexing. Their
composite over all coordinates is a projector `normalize` with image `N` and kernel `D`. Hence
`Aₙ = Nₙ ⊕ Dₙ`, and the inclusion of the normalized complex followed by the projection to the
quotient by degenerate cubes is an isomorphism of complexes, natural in the cubical module.

For the cubical cycle complexes of Bloch's higher Chow groups, both descriptions occur: the
cycles all of whose faces at `∞` vanish, and all admissible cycles modulo the degenerate ones.
The isomorphism here identifies the two, compatibly with every map of cycle complexes that
commutes with faces and degeneracies.

## Main definitions

* `TauCeti.CubicalModule.normalized`: the normalized `n`-cubes `⋂ᵢ ker ∂ᵢ^∞`.
* `TauCeti.CubicalModule.degenerate`: the degenerate `n`-cubes `∑ᵢ im sᵢ`.
* `TauCeti.CubicalModule.normalizeAt`: the elementary projector `1 - sᵢ ∘ ∂ᵢ^∞`.
* `TauCeti.CubicalModule.normalize`: the normalization projector, the composite of the elementary
  projectors in all coordinates.
* `TauCeti.CubicalModule.normalizedComplex`: the normalized cubical complex.
* `TauCeti.CubicalModule.degeneracyQuotientComplex`: the quotient of the cubical boundary complex
  by the degenerate cubes.
* `TauCeti.CubicalModule.normalizedComplexIsoDegeneracyQuotient`: the isomorphism of complexes
  between them.
* `TauCeti.CubicalModule.normalizedComplexFunctorIsoDegeneracyQuotient`: the same isomorphism,
  natural in the cubical module.

## Main results

* `TauCeti.CubicalModule.isCompl_normalized_degenerate`: `Aₙ = Nₙ ⊕ Dₙ`.
* `TauCeti.CubicalModule.range_normalize`, `TauCeti.CubicalModule.ker_normalize`: the
  normalization projector has image `N` and kernel `D`.
* `TauCeti.CubicalModule.boundary_mem_normalized`, `TauCeti.CubicalModule.boundary_mem_degenerate`:
  `N` and `D` are subcomplexes.
* `TauCeti.CubicalModule.normalizedComplexIsoDegeneracyQuotient_hom`: the isomorphism is the
  inclusion followed by the projection.
* `TauCeti.CubicalModule.const_normalized_succ`: the normalized complex of a constant cubical
  module is concentrated in degree `0`.

## References

* J. I. Burgos Gil and E. Feliu, *Higher arithmetic Chow groups*, Comment. Math. Helv. 87 (2012),
  521–587; arXiv:0907.5169, §1.6 and §2.1.
* M. Levine, *Bloch's higher Chow groups revisited*, Astérisque 226 (1994), 235–320.
-/

public section

noncomputable section

open CategoryTheory

universe v u

namespace TauCeti.CubicalModule

variable {R : Type u} [Ring R] (A : CubicalModule.{v} R)

/-! ### Normalized and degenerate cubes -/

/-- The **normalized** `n`-cubes `⋂ᵢ ker ∂ᵢ^∞`, those whose faces at `∞` all vanish. Every
`0`-cube is normalized. -/
def normalized : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊤
  | n + 1 => ⨅ i : Fin (n + 1), LinearMap.ker (A.face i true)

@[simp]
theorem normalized_zero : A.normalized 0 = ⊤ :=
  (rfl)

theorem normalized_succ (n : ℕ) :
    A.normalized (n + 1) = ⨅ i : Fin (n + 1), LinearMap.ker (A.face i true) :=
  (rfl)

@[simp]
theorem mem_normalized_succ_iff {n : ℕ} {x : A.X (n + 1)} :
    x ∈ A.normalized (n + 1) ↔ ∀ i, A.face i true x = 0 := by
  simp [normalized_succ]

/-- The **degenerate** `n`-cubes `∑ᵢ im sᵢ`, spanned by the images of the degeneracies. No
`0`-cube is degenerate. -/
def degenerate : (n : ℕ) → Submodule R (A.X n)
  | 0 => ⊥
  | n + 1 => ⨆ i : Fin (n + 1), LinearMap.range (A.degen i)

@[simp]
theorem degenerate_zero : A.degenerate 0 = ⊥ :=
  (rfl)

theorem degenerate_succ (n : ℕ) :
    A.degenerate (n + 1) = ⨆ i : Fin (n + 1), LinearMap.range (A.degen i) :=
  (rfl)

theorem degen_mem_degenerate {n : ℕ} (i : Fin (n + 1)) (x : A.X n) :
    A.degen i x ∈ A.degenerate (n + 1) := by
  rw [degenerate_succ]
  exact Submodule.mem_iSup_of_mem i (LinearMap.mem_range_self _ x)

/-- To check that the degenerate cubes lie in a submodule, it suffices to check the images of
the degeneracies. -/
theorem degenerate_succ_le_iff {n : ℕ} {p : Submodule R (A.X (n + 1))} :
    A.degenerate (n + 1) ≤ p ↔ ∀ i x, A.degen i x ∈ p := by
  simp only [degenerate_succ, iSup_le_iff]
  refine forall_congr' fun i ↦ ⟨fun h x ↦ h (LinearMap.mem_range_self _ x), ?_⟩
  rintro h _ ⟨x, rfl⟩
  exact h x

/-! ### The elementary projectors -/

/-- The **elementary normalization** `1 - sᵢ ∘ ∂ᵢ^∞` in the `i`-th coordinate. -/
def normalizeAt {n : ℕ} (i : Fin (n + 1)) : Module.End R (A.X (n + 1)) :=
  LinearMap.id - A.degen i ∘ₗ A.face i true

theorem normalizeAt_apply {n : ℕ} (i : Fin (n + 1)) (x : A.X (n + 1)) :
    A.normalizeAt i x = x - A.degen i (A.face i true x) :=
  (rfl)

@[simp]
theorem face_normalizeAt_self {n : ℕ} (i : Fin (n + 1)) (x : A.X (n + 1)) :
    A.face i true (A.normalizeAt i x) = 0 := by
  simp [normalizeAt_apply]

theorem normalizeAt_of_face_eq_zero {n : ℕ} {i : Fin (n + 1)} {x : A.X (n + 1)}
    (hx : A.face i true x = 0) : A.normalizeAt i x = x := by
  simp [normalizeAt_apply, hx]

@[simp]
theorem normalizeAt_degen_self {n : ℕ} (i : Fin (n + 1)) (x : A.X n) :
    A.normalizeAt i (A.degen i x) = 0 := by
  simp [normalizeAt_apply]

theorem sub_normalizeAt_mem_degenerate {n : ℕ} (i : Fin (n + 1)) (x : A.X (n + 1)) :
    x - A.normalizeAt i x ∈ A.degenerate (n + 1) := by
  simpa [normalizeAt_apply] using A.degen_mem_degenerate i _

/-- An `∞`-face in another coordinate turns an elementary projector into the elementary projector
in the reindexed coordinate. -/
theorem face_succAbove_normalizeAt {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1))
    (x : A.X (n + 2)) :
    A.face (i.succAbove k) true (A.normalizeAt i x) =
      A.normalizeAt (k.predAbove i) (A.face (i.succAbove k) true x) := by
  rw [normalizeAt_apply, normalizeAt_apply, map_sub, face_succAbove_degen, face_face]

/-- An elementary projector in another coordinate commutes with a degeneracy, up to reindexing. -/
theorem normalizeAt_succAbove_degen {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1))
    (x : A.X (n + 1)) :
    A.normalizeAt (j.succAbove k) (A.degen j x) = A.degen j (A.normalizeAt k x) := by
  rw [normalizeAt_apply, normalizeAt_apply, face_succAbove_degen, ← degen_degen, map_sub]

/-- Every elementary projector preserves the kernel of each `∞`-face. -/
theorem face_normalizeAt_eq_zero {n : ℕ} (i k : Fin (n + 1)) {x : A.X (n + 1)}
    (hx : A.face k true x = 0) : A.face k true (A.normalizeAt i x) = 0 := by
  obtain rfl | hki := eq_or_ne k i
  · exact A.face_normalizeAt_self k x
  cases n with
  | zero => exact absurd (Subsingleton.elim (α := Fin 1) k i) hki
  | succ n =>
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hki
    rw [face_succAbove_normalizeAt, hx, map_zero]

/-- Every elementary projector preserves the image of each degeneracy. -/
theorem normalizeAt_degen_mem_range {n : ℕ} (i j : Fin (n + 1)) (x : A.X n) :
    A.normalizeAt i (A.degen j x) ∈ LinearMap.range (A.degen j) := by
  obtain rfl | hij := eq_or_ne i j
  · simp
  cases n with
  | zero => exact absurd (Subsingleton.elim (α := Fin 1) i j) hij
  | succ n =>
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hij
    rw [normalizeAt_succAbove_degen]
    exact LinearMap.mem_range_self _ _

/-! ### Composites of elementary projectors -/

section List

variable {n : ℕ} (L : List (Fin (n + 1)))

private theorem face_listProd_normalizeAt {k : Fin (n + 1)} (hk : k ∈ L) (x : A.X (n + 1)) :
    A.face k true ((L.map A.normalizeAt).prod x) = 0 := by
  induction L with
  | nil => simp at hk
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    obtain rfl | hk := List.mem_cons.1 hk
    · exact A.face_normalizeAt_self k _
    · exact A.face_normalizeAt_eq_zero i k (ih hk)

private theorem listProd_normalizeAt_of_forall {x : A.X (n + 1)}
    (hx : ∀ k ∈ L, A.face k true x = 0) : (L.map A.normalizeAt).prod x = x := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp,
      ih fun k hk ↦ hx k (List.mem_cons_of_mem i hk),
      A.normalizeAt_of_face_eq_zero (hx i List.mem_cons_self)]

private theorem listProd_normalizeAt_degen_mem_range (j : Fin (n + 1)) (x : A.X n) :
    (L.map A.normalizeAt).prod (A.degen j x) ∈ LinearMap.range (A.degen j) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    obtain ⟨y, hy⟩ := ih
    rw [← hy]
    exact A.normalizeAt_degen_mem_range i j y

private theorem listProd_normalizeAt_degen {j : Fin (n + 1)} (hj : j ∈ L) (x : A.X n) :
    (L.map A.normalizeAt).prod (A.degen j x) = 0 := by
  induction L with
  | nil => simp at hj
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp]
    by_cases hjL : j ∈ L
    · rw [ih hjL, map_zero]
    · obtain rfl : j = i := (List.mem_cons.1 hj).resolve_right hjL
      obtain ⟨y, hy⟩ := A.listProd_normalizeAt_degen_mem_range L j x
      rw [← hy, normalizeAt_degen_self]

private theorem sub_listProd_normalizeAt_mem_degenerate (x : A.X (n + 1)) :
    x - (L.map A.normalizeAt).prod x ∈ A.degenerate (n + 1) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    rw [List.map_cons, List.prod_cons, mul_apply_eq_comp,
      ← sub_add_sub_cancel x ((L.map A.normalizeAt).prod x)]
    exact add_mem ih (A.sub_normalizeAt_mem_degenerate i _)

end List

/-! ### The normalization projector -/

/-- The **normalization projector**: on `(n + 1)`-cubes, the composite
`(1 - s₀ ∘ ∂₀^∞) ∘ ⋯ ∘ (1 - sₙ ∘ ∂ₙ^∞)` of the elementary projectors; the identity on
`0`-cubes. Its image is the normalized cubes and its kernel the degenerate cubes. -/
def normalize : (n : ℕ) → Module.End R (A.X n)
  | 0 => 1
  | n + 1 => (List.ofFn fun i : Fin (n + 1) ↦ A.normalizeAt i).prod

@[simp]
theorem normalize_zero : A.normalize 0 = 1 :=
  (rfl)

theorem normalize_succ (n : ℕ) :
    A.normalize (n + 1) = (List.ofFn fun i : Fin (n + 1) ↦ A.normalizeAt i).prod :=
  (rfl)

private theorem normalize_succ_eq_listProd (n : ℕ) :
    A.normalize (n + 1) = ((List.finRange (n + 1)).map A.normalizeAt).prod := by
  rw [normalize_succ, List.ofFn_eq_map]

/-- The normalization projector lands in the normalized cubes. -/
theorem normalize_mem_normalized (n : ℕ) (x : A.X n) : A.normalize n x ∈ A.normalized n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [mem_normalized_succ_iff, normalize_succ_eq_listProd]
    exact fun k ↦ A.face_listProd_normalizeAt _ (List.mem_finRange k) x

/-- The normalization projector fixes the normalized cubes. -/
theorem normalize_eq_self {n : ℕ} {x : A.X n} (hx : x ∈ A.normalized n) :
    A.normalize n x = x := by
  cases n with
  | zero => simp
  | succ n =>
    rw [normalize_succ_eq_listProd]
    exact A.listProd_normalizeAt_of_forall _ fun k _ ↦ (A.mem_normalized_succ_iff.1 hx) k

@[simp]
theorem normalize_degen {n : ℕ} (i : Fin (n + 1)) (x : A.X n) :
    A.normalize (n + 1) (A.degen i x) = 0 := by
  rw [normalize_succ_eq_listProd]
  exact A.listProd_normalizeAt_degen _ (List.mem_finRange i) x

/-- The normalization projector kills the degenerate cubes. -/
theorem normalize_eq_zero {n : ℕ} {x : A.X n} (hx : x ∈ A.degenerate n) :
    A.normalize n x = 0 := by
  cases n with
  | zero => simp_all
  | succ n =>
    have : A.degenerate (n + 1) ≤ LinearMap.ker (A.normalize (n + 1)) :=
      A.degenerate_succ_le_iff.2 fun i y ↦ A.normalize_degen i y
    exact this hx

/-- Every cube differs from its normalization by a degenerate cube. -/
theorem sub_normalize_mem_degenerate (n : ℕ) (x : A.X n) :
    x - A.normalize n x ∈ A.degenerate n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [normalize_succ_eq_listProd]
    exact A.sub_listProd_normalizeAt_mem_degenerate _ x

@[simp]
theorem normalize_normalize (n : ℕ) (x : A.X n) :
    A.normalize n (A.normalize n x) = A.normalize n x :=
  A.normalize_eq_self (A.normalize_mem_normalized n x)

/-- The image of the normalization projector is the normalized cubes. -/
theorem range_normalize (n : ℕ) : LinearMap.range (A.normalize n) = A.normalized n :=
  le_antisymm
    (LinearMap.range_le_iff_comap.2 <| eq_top_iff.2 fun x _ ↦ A.normalize_mem_normalized n x)
    fun x hx ↦ ⟨x, A.normalize_eq_self hx⟩

/-- The kernel of the normalization projector is the degenerate cubes. -/
theorem ker_normalize (n : ℕ) : LinearMap.ker (A.normalize n) = A.degenerate n :=
  le_antisymm
    (fun x hx ↦ by simpa [LinearMap.mem_ker.1 hx] using A.sub_normalize_mem_degenerate n x)
    fun _ hx ↦ A.normalize_eq_zero hx

/-- Every module of cubes is the direct sum of its normalized and its degenerate cubes. -/
theorem isCompl_normalized_degenerate (n : ℕ) : IsCompl (A.normalized n) (A.degenerate n) := by
  rw [← A.range_normalize, ← A.ker_normalize]
  exact LinearMap.IsIdempotentElem.isCompl (LinearMap.ext (A.normalize_normalize n))

/-! ### The boundary on normalized and degenerate cubes -/

theorem face_face_eq_zero_of_mem_normalized {n : ℕ} {x : A.X (n + 2)}
    (hx : x ∈ A.normalized (n + 2)) (i : Fin (n + 2)) (k : Fin (n + 1)) (ε : Bool) :
    A.face k true (A.face i ε x) = 0 := by
  rw [face_face, (A.mem_normalized_succ_iff.1 hx) _, map_zero]

/-- The boundary of a normalized cube is normalized. -/
theorem boundary_mem_normalized {n : ℕ} {x : A.X (n + 1)} (hx : x ∈ A.normalized (n + 1)) :
    A.boundary n x ∈ A.normalized n := by
  cases n with
  | zero => simp
  | succ n =>
    simp [mem_normalized_succ_iff, boundary_apply, faceDiff_apply,
      A.face_face_eq_zero_of_mem_normalized hx]

/-- On normalized cubes, the cubical boundary is `∑ᵢ (-1)ⁱ ∂ᵢ⁰`. -/
theorem boundary_apply_of_mem_normalized {n : ℕ} {x : A.X (n + 1)}
    (hx : x ∈ A.normalized (n + 1)) :
    A.boundary n x = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • A.face i false x := by
  simp [boundary_apply, faceDiff_apply, A.mem_normalized_succ_iff.1 hx]

theorem faceDiff_degen_mem_degenerate {n : ℕ} (i j : Fin (n + 1)) (x : A.X n) :
    A.faceDiff i (A.degen j x) ∈ A.degenerate n := by
  obtain rfl | hij := eq_or_ne i j
  · simp [faceDiff_apply]
  cases n with
  | zero => exact absurd (Subsingleton.elim (α := Fin 1) i j) hij
  | succ n =>
    obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hij
    rw [faceDiff_apply, face_succAbove_degen, face_succAbove_degen]
    exact sub_mem (A.degen_mem_degenerate _ _) (A.degen_mem_degenerate _ _)

/-- The boundary of a degenerate cube is degenerate. -/
theorem boundary_mem_degenerate {n : ℕ} {x : A.X (n + 1)} (hx : x ∈ A.degenerate (n + 1)) :
    A.boundary n x ∈ A.degenerate n := by
  have : A.degenerate (n + 1) ≤ (A.degenerate n).comap (A.boundary n) :=
    A.degenerate_succ_le_iff.2 fun j y ↦ by
      rw [Submodule.mem_comap, boundary_apply]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_of_tower_mem _ _ (A.faceDiff_degen_mem_degenerate i j y)
  exact this hx

variable {A} in
/-- A linear map sending normalized cubes to normalized cubes and degenerate cubes to degenerate
cubes commutes with the normalization projectors. -/
theorem normalize_comp_of_le {B : CubicalModule.{v} R} {m n : ℕ} (f : A.X m →ₗ[R] B.X n)
    (hN : A.normalized m ≤ (B.normalized n).comap f)
    (hD : A.degenerate m ≤ (B.degenerate n).comap f) :
    B.normalize n ∘ₗ f = f ∘ₗ A.normalize m := by
  ext x
  have h := B.normalize_eq_zero (hD (A.sub_normalize_mem_degenerate m x))
  rw [map_sub, map_sub, sub_eq_zero] at h
  rw [LinearMap.comp_apply, h, B.normalize_eq_self (hN (A.normalize_mem_normalized m x)),
    LinearMap.comp_apply]

/-- The normalization projector commutes with the cubical boundary. -/
theorem normalize_boundary (n : ℕ) (x : A.X (n + 1)) :
    A.normalize n (A.boundary n x) = A.boundary n (A.normalize (n + 1) x) :=
  congr($(normalize_comp_of_le (A.boundary n) (fun _ ↦ A.boundary_mem_normalized)
    fun _ ↦ A.boundary_mem_degenerate) x)

/-! ### The normalized complex and the degeneracy quotient -/

/-- The cubical boundary restricted to the normalized cubes. -/
def normalizedBoundary (n : ℕ) : A.normalized (n + 1) →ₗ[R] A.normalized n :=
  (A.boundary n).restrict fun _ hx ↦ A.boundary_mem_normalized hx

@[simp]
theorem coe_normalizedBoundary_apply (n : ℕ) (x : A.normalized (n + 1)) :
    (A.normalizedBoundary n x : A.X n) = A.boundary n x :=
  (rfl)

/-- The cubical boundary induced on the quotient by the degenerate cubes. -/
def degeneracyQuotientBoundary (n : ℕ) :
    (A.X (n + 1) ⧸ A.degenerate (n + 1)) →ₗ[R] A.X n ⧸ A.degenerate n :=
  (A.degenerate (n + 1)).mapQ (A.degenerate n) (A.boundary n) fun _ hx ↦
    A.boundary_mem_degenerate hx

@[simp]
theorem degeneracyQuotientBoundary_mk (n : ℕ) (x : A.X (n + 1)) :
    A.degeneracyQuotientBoundary n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (A.boundary n x) :=
  (rfl)

/-- The **normalized cubical complex**: the normalized cubes `⋂ᵢ ker ∂ᵢ^∞` with the cubical
boundary, which on them is `∑ᵢ (-1)ⁱ ∂ᵢ⁰`. -/
@[expose] def normalizedComplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (A.normalized n))
    (fun n ↦ ModuleCat.ofHom (A.normalizedBoundary n)) fun n ↦ by
      ext x
      simp

/-- The **degeneracy quotient complex**: the quotient of the cubical boundary complex by the
degenerate cubes. -/
@[expose] def degeneracyQuotientComplex : ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (A.X n ⧸ A.degenerate n))
    (fun n ↦ ModuleCat.ofHom (A.degeneracyQuotientBoundary n)) fun n ↦ by
      ext x
      simp

@[simp]
theorem normalizedComplex_X (n : ℕ) : A.normalizedComplex.X n = ModuleCat.of R (A.normalized n) :=
  (rfl)

theorem normalizedComplex_d (n : ℕ) :
    A.normalizedComplex.d (n + 1) n = ModuleCat.ofHom (A.normalizedBoundary n) := by
  simp only [normalizedComplex, ChainComplex.of_d]

@[simp]
theorem normalizedComplex_d_apply (n : ℕ) (x : A.normalized (n + 1)) :
    A.normalizedComplex.d (n + 1) n x = A.normalizedBoundary n x := by
  rw [normalizedComplex_d]
  -- The two sides differ only in the module instances on the carrier of `ModuleCat.of`.
  rfl

@[simp]
theorem degeneracyQuotientComplex_X (n : ℕ) :
    A.degeneracyQuotientComplex.X n = ModuleCat.of R (A.X n ⧸ A.degenerate n) :=
  (rfl)

theorem degeneracyQuotientComplex_d (n : ℕ) :
    A.degeneracyQuotientComplex.d (n + 1) n = ModuleCat.ofHom (A.degeneracyQuotientBoundary n) := by
  simp only [degeneracyQuotientComplex, ChainComplex.of_d]

@[simp]
theorem degeneracyQuotientComplex_d_mk (n : ℕ) (x : A.X (n + 1)) :
    A.degeneracyQuotientComplex.d (n + 1) n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (A.boundary n x) := by
  rw [degeneracyQuotientComplex_d]
  -- The two sides differ only in the module instances on the carrier of `ModuleCat.of`.
  rfl

/-- The inclusion of the normalized complex into the cubical boundary complex. -/
def normalizedComplexι : A.normalizedComplex ⟶ A.complex :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (A.normalized n).subtype) fun n ↦ by
    rw [complex_d, normalizedComplex_d]
    exact ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq
      (LinearMap.ext fun x ↦ (A.coe_normalizedBoundary_apply n x).symm)

@[simp]
theorem normalizedComplexι_f_apply (n : ℕ) (x : A.normalized n) :
    A.normalizedComplexι.f n x = (x : A.X n) :=
  (rfl)

/-- The projection of the cubical boundary complex onto its degeneracy quotient. -/
def degeneracyQuotientComplexπ : A.complex ⟶ A.degeneracyQuotientComplex :=
  ChainComplex.ofHom (fun n ↦ ModuleCat.ofHom (A.degenerate n).mkQ) fun n ↦ by
    rw [complex_d, degeneracyQuotientComplex_d]
    exact ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq
      (LinearMap.ext (A.degeneracyQuotientBoundary_mk n))

@[simp]
theorem degeneracyQuotientComplexπ_f_apply (n : ℕ) (x : A.X n) :
    A.degeneracyQuotientComplexπ.f n x = Submodule.Quotient.mk x :=
  (rfl)

/-- The linear equivalence between the normalized `n`-cubes and the `n`-cubes modulo degenerate
ones, induced by the inclusion. -/
def normalizedEquivDegeneracyQuotient (n : ℕ) : A.normalized n ≃ₗ[R] A.X n ⧸ A.degenerate n :=
  (Submodule.quotientEquivOfIsCompl _ _ (A.isCompl_normalized_degenerate n).symm).symm

@[simp]
theorem normalizedEquivDegeneracyQuotient_apply (n : ℕ) (x : A.normalized n) :
    A.normalizedEquivDegeneracyQuotient n x = Submodule.Quotient.mk (x : A.X n) :=
  (rfl)

/-- The inverse of `normalizedEquivDegeneracyQuotient` is induced by the normalization
projector. -/
@[simp]
theorem normalizedEquivDegeneracyQuotient_symm_mk (n : ℕ) (x : A.X n) :
    (A.normalizedEquivDegeneracyQuotient n).symm (Submodule.Quotient.mk x) =
      ⟨A.normalize n x, A.normalize_mem_normalized n x⟩ := by
  rw [LinearEquiv.symm_apply_eq, normalizedEquivDegeneracyQuotient_apply]
  exact (Submodule.Quotient.eq _).2 (A.sub_normalize_mem_degenerate n x)

/-- The **normalized complex is isomorphic to the degeneracy quotient complex**, by the inclusion
of the normalized cubes followed by the projection to the quotient by the degenerate cubes. -/
def normalizedComplexIsoDegeneracyQuotient :
    A.normalizedComplex ≅ A.degeneracyQuotientComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (A.normalizedEquivDegeneracyQuotient n).toModuleIso) fun i j hij ↦ by
      obtain rfl : i = j + 1 := hij.symm
      rw [normalizedComplex_d, degeneracyQuotientComplex_d]
      rw [LinearEquiv.toModuleIso_hom, LinearEquiv.toModuleIso_hom]
      -- The components agree by `normalizedEquivDegeneracyQuotient_apply` and
      -- `degeneracyQuotientBoundary_mk`.
      exact ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq
        (LinearMap.ext fun x : A.normalized (j + 1) ↦ by simp)

@[simp]
theorem normalizedComplexIsoDegeneracyQuotient_hom :
    A.normalizedComplexIsoDegeneracyQuotient.hom =
      A.normalizedComplexι ≫ A.degeneracyQuotientComplexπ := by
  -- The components of both sides are the inclusion followed by the projection, as maps between
  -- objects that agree with `A.normalizedComplex.X n` and `A.degeneracyQuotientComplex.X n` only
  -- up to unfolding, so `rw` and `simp` cannot match them.
  ext n : 1
  rfl

/-- The inverse of `normalizedComplexIsoDegeneracyQuotient` is induced by the normalization
projector. -/
@[simp]
theorem normalizedComplexIsoDegeneracyQuotient_inv_f_mk (n : ℕ) (x : A.X n) :
    A.normalizedComplexIsoDegeneracyQuotient.inv.f n (Submodule.Quotient.mk x) =
      (⟨A.normalize n x, A.normalize_mem_normalized n x⟩ : A.normalized n) :=
  A.normalizedEquivDegeneracyQuotient_symm_mk n x

/-! ### Naturality -/

variable {A} {B : CubicalModule.{v} R}

/-- A morphism of cubical modules preserves normalized cubes. -/
theorem Hom.f_mem_normalized (φ : A ⟶ B) {n : ℕ} {x : A.X n} (hx : x ∈ A.normalized n) :
    φ.f n x ∈ B.normalized n := by
  cases n with
  | zero => simp
  | succ n => simp_all

/-- A morphism of cubical modules preserves degenerate cubes. -/
theorem Hom.f_mem_degenerate (φ : A ⟶ B) {n : ℕ} {x : A.X n} (hx : x ∈ A.degenerate n) :
    φ.f n x ∈ B.degenerate n := by
  cases n with
  | zero => simp_all
  | succ n =>
    have : A.degenerate (n + 1) ≤ (B.degenerate (n + 1)).comap (φ.f (n + 1)) :=
      A.degenerate_succ_le_iff.2 fun i y ↦ by
        rw [Submodule.mem_comap, ← Hom.degen_f]
        exact B.degen_mem_degenerate i _
    exact this hx

/-- A morphism of cubical modules commutes with the normalization projectors. -/
theorem Hom.f_normalize (φ : A ⟶ B) (n : ℕ) (x : A.X n) :
    φ.f n (A.normalize n x) = B.normalize n (φ.f n x) :=
  congr($(normalize_comp_of_le (φ.f n) (fun _ ↦ φ.f_mem_normalized)
    fun _ ↦ φ.f_mem_degenerate) x).symm

/-- The **normalized cubical complex functor**, sending a cubical module to its normalized
cubical complex. -/
@[expose] def normalizedComplexFunctor :
    CubicalModule.{v} R ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj A := A.normalizedComplex
  map φ := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom ((φ.f n).restrict fun _ hx ↦ φ.f_mem_normalized hx)) fun n ↦ by
      rw [normalizedComplex_d, normalizedComplex_d]
      exact ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq
        (LinearMap.ext fun x : _ ↦ Subtype.ext (φ.boundary_f x.val))

@[simp]
theorem normalizedComplexFunctor_obj : normalizedComplexFunctor.obj A = A.normalizedComplex :=
  (rfl)

@[simp]
theorem normalizedComplexFunctor_map_f_apply (φ : A ⟶ B) (n : ℕ) (x : A.normalized n) :
    (normalizedComplexFunctor.map φ).f n x = ⟨φ.f n x, φ.f_mem_normalized x.property⟩ :=
  (rfl)

/-- The **degeneracy quotient complex functor**, sending a cubical module to the quotient of its
cubical boundary complex by the degenerate cubes. -/
@[expose] def degeneracyQuotientComplexFunctor :
    CubicalModule.{v} R ⥤ ChainComplex (ModuleCat.{v} R) ℕ where
  obj A := A.degeneracyQuotientComplex
  map {A B} φ := ChainComplex.ofHom
    (fun n ↦ ModuleCat.ofHom ((A.degenerate n).mapQ (B.degenerate n) (φ.f n) fun _ hx ↦
      φ.f_mem_degenerate hx)) fun n ↦ by
      rw [degeneracyQuotientComplex_d, degeneracyQuotientComplex_d]
      exact ModuleCat.ofHom_comp_ofHom_eq_of_comp_eq (Submodule.linearMap_qext _
        (LinearMap.ext fun x ↦ congr_arg Submodule.Quotient.mk (φ.boundary_f x)))
  -- On a class `[x]`, both sides of `map_id` are `[x]` and both sides of `map_comp` are
  -- `[ψ (φ x)]` by the definition of `mapQ`; `degeneracyQuotientComplexFunctor_map_f_mk` is only
  -- available after this declaration.
  map_id A := by
    ext n x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl
  map_comp φ ψ := by
    ext n x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl

@[simp]
theorem degeneracyQuotientComplexFunctor_obj :
    degeneracyQuotientComplexFunctor.obj A = A.degeneracyQuotientComplex :=
  (rfl)

@[simp]
theorem degeneracyQuotientComplexFunctor_map_f_mk (φ : A ⟶ B) (n : ℕ) (x : A.X n) :
    (degeneracyQuotientComplexFunctor.map φ).f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ.f n x) :=
  (rfl)

/-- The inclusion of the normalized complex, natural in the cubical module. -/
def normalizedComplexFunctorι : normalizedComplexFunctor ⟶ complexFunctor (R := R) where
  app A := A.normalizedComplexι

@[simp]
theorem normalizedComplexFunctorι_app : normalizedComplexFunctorι.app A = A.normalizedComplexι :=
  (rfl)

/-- The projection onto the degeneracy quotient complex, natural in the cubical module. -/
def degeneracyQuotientComplexFunctorπ :
    complexFunctor ⟶ degeneracyQuotientComplexFunctor (R := R) where
  app A := A.degeneracyQuotientComplexπ

@[simp]
theorem degeneracyQuotientComplexFunctorπ_app :
    degeneracyQuotientComplexFunctorπ.app A = A.degeneracyQuotientComplexπ :=
  (rfl)

/-- The isomorphism `normalizedComplexIsoDegeneracyQuotient`, natural in the cubical module. -/
def normalizedComplexFunctorIsoDegeneracyQuotient :
    normalizedComplexFunctor ≅ degeneracyQuotientComplexFunctor (R := R) :=
  NatIso.ofComponents (fun A ↦ A.normalizedComplexIsoDegeneracyQuotient) fun φ ↦ by
    -- Both components send `x` to the class of `φ x`, between objects that agree with the
    -- functors' objects only up to unfolding.
    simp only [normalizedComplexIsoDegeneracyQuotient_hom]
    ext n x
    rfl

@[simp]
theorem normalizedComplexFunctorIsoDegeneracyQuotient_hom :
    normalizedComplexFunctorIsoDegeneracyQuotient.hom =
      normalizedComplexFunctorι (R := R) ≫ degeneracyQuotientComplexFunctorπ := by
  ext A : 2
  exact A.normalizedComplexIsoDegeneracyQuotient_hom


/-! ### Constant cubical modules -/

section const

variable (M : ModuleCat.{v} R)

/-- A constant cubical module has no nonzero normalized cubes in positive degrees, so its
normalized complex is concentrated in degree `0`. -/
@[simp]
theorem const_normalized_succ (n : ℕ) : (const M).normalized (n + 1) = ⊥ := by
  ext x
  simp only [mem_normalized_succ_iff, const_face, Submodule.mem_bot]
  exact ⟨fun h ↦ h 0, fun h _ ↦ h⟩

/-- Every positive-dimensional cube of a constant cubical module is degenerate. -/
@[simp]
theorem const_degenerate_succ (n : ℕ) : (const M).degenerate (n + 1) = ⊤ :=
  eq_top_iff.2 fun x _ ↦ (const M).degen_mem_degenerate (n := n) 0 x

end const

end TauCeti.CubicalModule
