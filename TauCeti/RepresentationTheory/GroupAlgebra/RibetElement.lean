/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Charpoly.Ribet
import TauCeti.LinearAlgebra.Matrix.Determinant.FromBlocks
import TauCeti.LinearAlgebra.Matrix.Trace.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Ideal

/-!
# Ribet's element for a matrix of tied rows

Let `O` be a commutative ring, `L` a commutative `O`-algebra, `G` a monoid and
`u x : O[G] →ₐ[O] Matrix σ σ O` (`x ∈ Y`) a family of representations. Let `S` be an `O`-subalgebra
of the functions `Y → L` containing, as functions of `x`, the coefficients of the characteristic
polynomials of the `u x g` for `g ∈ G`, and let `𝒥` be an `S`-submodule of the functions `Y → L`.
A row of elements of `O[G]` is *tied* to `y ∈ O[G]^N` modulo `ρ₀ ∈ O[G]` when its product with `y`
lies in `𝔞 + I ρ₀`, where `I` is the left ideal spanned by the entries of `y` and `𝔞` is the left
ideal spanned by the `w` such that `x ↦ tr u x (w g)` lies in `𝒥` for every `g ∈ G`.

`TauCeti.exists_ribet_element_of_tied_rows` shows that for a square matrix `B` of tied rows and
every `ρ₁ ∈ O[G]`, a single `f ∈ S` multiplies the functions `x ↦ det u x w` (`w ∈ I`) into `𝒥`,
and takes the value `det (u x B) * tr u x ρ₁` at every `x` with `u x (ρ₁ ρ₀) = 0`; here
`det (u x B)` is the determinant of the block matrix `(u x (B i j))_{i,j}`.

`TauCeti.exists_ribet_element_of_tied_rows_of_blocks` is the form used in Ribet's method: on a set
`𝓧 ⊆ Y` where every `u x` is the block sum of a representation `ψ x` and of characters `η t`, with
`ρ₁` killed by `ψ x` and by every `η t` but `η t₀`, on which it is `μ₀`, and `η t₀ ρ₀ = 0`, the
element `f` takes at `x ∈ 𝓧` the value `μ₀ * det (ψ x B) * ∏ t, det (η t B)`.

## Implementation notes

The family `u` is one representation `ρ` of `S[G]` over the ring of functions `Y → L`, whose
characteristic polynomials have coefficients in `S` by Amitsur's theorem
(`AlgHom.charpoly_coeff_mem_range_of_span`), since they do on the elements of `G`. Ribet's
polynomial (`AlgHom.exists_ribet_polynomial`) for `ρ`, with the two-sided ideal
`TauCeti.traceIdeal ρ 𝒥` of the elements whose traces against `S[G]` lie in `𝒥`, gives
`P ∈ S[X]`, and `f` is the trace of `ρ (ρ₁ P(ρ₀))`.

## References

* K. A. Ribet, *A modular construction of unramified p-extensions of `ℚ(μ_p)`*, Invent. Math.
  **34** (1976), 151–162.
* J. Bellaïche and G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque **324** (2009), Chapter 1.

## Provenance

The statement and the route through a representation of `S[G]` follow
`New.Selmer.exists_ribet_element_of_tied_rows` (file
`src/New/Congruences/FirstOrder/RibetMethod.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Matrix Polynomial MonoidAlgebra

namespace TauCeti

variable {O L Y G σ N : Type*} [CommRing O] [CommRing L] [Algebra O L] [Monoid G]
  [Fintype σ] [DecidableEq σ] [Fintype N] [DecidableEq N]

/-- The family `u` as one representation of `O[G]` over the ring of functions `Y → L`. -/
private noncomputable def familyAlgHom (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O) :
    MonoidAlgebra O G →ₐ[O] Matrix σ σ (Y → L) :=
  (piAlgEquiv O).symm.toAlgHom.comp
    (AlgHom.pi fun x ↦ (Algebra.ofId O L).mapMatrix.comp (u x))

@[simp]
private theorem familyAlgHom_apply (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (r : MonoidAlgebra O G) (i j : σ) (x : Y) :
    familyAlgHom (L := L) u r i j x = algebraMap O L (u x r i j) := by
  simp [familyAlgHom]

private theorem evalRingHom_mapMatrix_familyAlgHom
    (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O) (x : Y) (r : MonoidAlgebra O G) :
    (Pi.evalRingHom (fun _ ↦ L) x).mapMatrix (familyAlgHom u r) =
      (algebraMap O L).mapMatrix (u x r) := by
  ext i j
  simp

private theorem trace_familyAlgHom (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (r : MonoidAlgebra O G) :
    (familyAlgHom (L := L) u r).trace = fun x ↦ algebraMap O L (u x r).trace := by
  funext x
  simp [Matrix.trace]

private theorem det_familyAlgHom (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (r : MonoidAlgebra O G) :
    (familyAlgHom (L := L) u r).det = fun x ↦ algebraMap O L (u x r).det := by
  funext x
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : Y ↦ L) x) (familyAlgHom u r)
  rwa [evalRingHom_mapMatrix_familyAlgHom, ← RingHom.map_det, Pi.evalRingHom_apply] at h

private theorem charpoly_familyAlgHom_coeff (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (r : MonoidAlgebra O G) (k : ℕ) :
    (familyAlgHom (L := L) u r).charpoly.coeff k =
      fun x ↦ algebraMap O L ((u x r).charpoly.coeff k) := by
  funext x
  have h := congrArg (·.coeff k)
    (charpoly_map (familyAlgHom u r) (Pi.evalRingHom (fun _ : Y ↦ L) x))
  rw [← RingHom.mapMatrix_apply, evalRingHom_mapMatrix_familyAlgHom] at h
  simpa [charpoly_map, Polynomial.coeff_map] using h.symm

/-- The family `u` as one representation of `S[G]` over the ring of functions `Y → L`. -/
private noncomputable def familyLift (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L)) : MonoidAlgebra S G →ₐ[S] Matrix σ σ (Y → L) :=
  MonoidAlgebra.lift S (Matrix σ σ (Y → L)) G
    ((familyAlgHom (L := L) u : MonoidAlgebra O G →* Matrix σ σ (Y → L)).comp (of O G))

private theorem familyLift_mapRingHom (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L)) (r : MonoidAlgebra O G) :
    familyLift u S (mapRingHom G (algebraMap O S) r) = familyAlgHom u r := by
  have : ((familyLift u S).restrictScalars O).comp (mapAlgHom G (Algebra.ofId O S)) =
      familyAlgHom u :=
    algHom_ext (fun g ↦ by simp [familyLift]) (Subsingleton.elim _ _)
  exact congr($this r)

/-- The characteristic polynomials of `familyLift u S` have coefficients in `S`, by Amitsur's
theorem, since those of the elements of `G` do. -/
private theorem familyLift_charpoly_coeff_mem (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L))
    (hS : ∀ (g : G) (k : ℕ), (fun x ↦ algebraMap O L ((u x (single g 1)).charpoly.coeff k)) ∈ S)
    (a : MonoidAlgebra S G) (k : ℕ) :
    (familyLift u S a).charpoly.coeff k ∈ (algebraMap S (Y → L)).range := by
  have hspan : Submodule.span S (Set.range (of S G)) = ⊤ :=
    eq_top_iff.2 fun a _ ↦ a.induction_on (fun g ↦ Submodule.subset_span ⟨g, rfl⟩)
      (fun _ _ ↦ add_mem) fun c _ h ↦ Submodule.smul_mem _ c h
  refine AlgHom.charpoly_coeff_mem_range_of_span _ hspan ?_ a k
  rintro _ ⟨g, rfl⟩ k
  refine ⟨⟨_, hS g k⟩, ?_⟩
  simp [familyLift, charpoly_familyAlgHom_coeff]

/-- The left ideal spanned by the `w` whose traces `x ↦ tr u x (w g)` lie in `𝒥` maps into the
trace ideal of `𝒥` along `familyLift u S`. -/
private theorem mapRingHom_mem_traceIdeal (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L)) (𝒥 : Submodule S (Y → L)) {a : MonoidAlgebra O G}
    (ha : a ∈ Submodule.span (MonoidAlgebra O G)
      {w | ∀ g : G, (fun x ↦ algebraMap O L (u x (w * single g 1)).trace) ∈ 𝒥}) :
    mapRingHom G (algebraMap O S) a ∈ traceIdeal (familyLift u S) 𝒥.toAddSubgroup := by
  induction ha using Submodule.span_induction with
  | zero => simp
  | add a a' _ _ ha ha' => simpa using TwoSidedIdeal.add_mem _ ha ha'
  | smul c a _ ha => simpa using TwoSidedIdeal.mul_mem_left _ _ _ ha
  | mem w hw =>
    refine mem_traceIdeal.2 fun s ↦ ?_
    induction s using MonoidAlgebra.induction_on with
    | of g =>
      have : of S G g = mapRingHom G (algebraMap O S) (single g 1) := by simp
      rw [this, ← map_mul, familyLift_mapRingHom, trace_familyAlgHom]
      exact hw g
    | add s s' hs hs' => simpa [mul_add] using add_mem hs hs'
    | smul c s hs => simpa using 𝒥.smul_mem c hs

/-- Where `ρ₁ ρ₀` acts as `0`, `ρ₁ P(ρ₀)` acts with the trace of `P(0) ρ₁`. -/
private theorem trace_familyLift_mul_aeval_apply (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L)) (ρ₀ ρ₁ : MonoidAlgebra O G) (P : (↥S)[X]) {x : Y}
    (hx : u x (ρ₁ * ρ₀) = 0) :
    (familyLift u S (mapRingHom G (algebraMap O S) ρ₁ *
        aeval (mapRingHom G (algebraMap O S) ρ₀) P)).trace x =
      (P.coeff 0 : Y → L) x * algebraMap O L (u x ρ₁).trace := by
  set ι := mapRingHom G (algebraMap O S)
  have hsplit : ι ρ₁ * aeval (ι ρ₀) P = ι (ρ₁ * ρ₀) * aeval (ι ρ₀) P.divX + P.coeff 0 • ι ρ₁ := by
    conv_lhs => rw [← P.X_mul_divX_add]
    simp only [map_add, map_mul, aeval_X, aeval_C, mul_add, mul_assoc, Algebra.smul_def]
    rw [Algebra.commutes]
  have h0 : (familyAlgHom u (ρ₁ * ρ₀) * familyLift u S (aeval (ι ρ₀) P.divX)).trace x = 0 := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply,
      familyAlgHom_apply, hx, Matrix.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  rw [hsplit, map_add, map_mul, map_smul, familyLift_mapRingHom, familyLift_mapRingHom]
  simp [-map_mul, h0, trace_familyAlgHom, Subalgebra.smul_def]

/-- At a point `x`, the determinant of the block matrix of `B` along `familyLift u S` is that of
the block matrix of `B` along `u x`. -/
private theorem det_comp_map_familyLift_apply (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L)) (B : Matrix N N (MonoidAlgebra O G)) (x : Y) :
    (comp N N σ σ (Y → L) ((B.map (mapRingHom G (algebraMap O S))).map (familyLift u S))).det x =
      algebraMap O L (comp N N σ σ O (B.map (u x))).det := by
  have h := RingHom.map_det (Pi.evalRingHom (fun _ : Y ↦ L) x)
    (comp N N σ σ (Y → L) ((B.map (mapRingHom G (algebraMap O S))).map (familyLift u S)))
  rw [Pi.evalRingHom_apply] at h
  rw [h, RingHom.map_det]
  congr 1
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [familyLift_mapRingHom]

/-- **Ribet's element for a matrix of tied rows.** Let `u x : O[G] →ₐ[O] Matrix σ σ O` (`x ∈ Y`) be
representations and `S` an `O`-subalgebra of the functions `Y → L` containing the functions
`x ↦` coefficients of the characteristic polynomial of `u x g`, for `g ∈ G`. Let `𝒥` be an
`S`-submodule of the functions `Y → L`, `I` the left ideal spanned by `y : N → O[G]`, `𝔞` the left
ideal spanned by the `w` such that `x ↦ tr u x (w g)` lies in `𝒥` for every `g ∈ G`, and `B` a
square matrix with `(B *ᵥ y) i ∈ 𝔞 + I ρ₀` for every `i`. Then for every `ρ₁` some `f ∈ S` has
`f * (x ↦ det u x w) ∈ 𝒥` for every `w ∈ I`, and at every `x` with `u x (ρ₁ * ρ₀) = 0`, `f x` is
the determinant of the block matrix `(u x (B i j))_{i,j}` times the trace of `u x ρ₁`. -/
theorem exists_ribet_element_of_tied_rows (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L))
    (hS : ∀ (g : G) (k : ℕ), (fun x ↦ algebraMap O L ((u x (single g 1)).charpoly.coeff k)) ∈ S)
    (𝒥 : Submodule S (Y → L)) (y : N → MonoidAlgebra O G) (ρ₀ ρ₁ : MonoidAlgebra O G)
    (B : Matrix N N (MonoidAlgebra O G))
    (hB : ∀ i, ∃ a ∈ Submodule.span (MonoidAlgebra O G)
        {w | ∀ g : G, (fun x ↦ algebraMap O L (u x (w * single g 1)).trace) ∈ 𝒥},
      ∃ z ∈ Submodule.span (MonoidAlgebra O G) (Set.range y), (B *ᵥ y) i = a + z * ρ₀) :
    ∃ f ∈ S, (∀ w ∈ Submodule.span (MonoidAlgebra O G) (Set.range y),
        f * (fun x ↦ algebraMap O L (u x w).det) ∈ 𝒥) ∧
      ∀ x, u x (ρ₁ * ρ₀) = 0 →
        f x = algebraMap O L ((comp N N σ σ O (B.map (u x))).det * (u x ρ₁).trace) := by
  let ρ := familyLift u S
  let ι := mapRingHom G (algebraMap O S)
  have hchar := familyLift_charpoly_coeff_mem u S hS
  let 𝔞 : TwoSidedIdeal (MonoidAlgebra S G) := traceIdeal ρ 𝒥.toAddSubgroup
  -- `ι` maps the left ideal spanned by `y` into the left ideal spanned by `ι ∘ y`.
  have hspan {w : MonoidAlgebra O G} (hw : w ∈ Submodule.span (MonoidAlgebra O G) (Set.range y)) :
      ι w ∈ Submodule.span (MonoidAlgebra S G) (Set.range (ι ∘ y)) := by
    have h := Ideal.mem_map_of_mem ι (I := Ideal.span (Set.range y)) hw
    rwa [Ideal.map_span, ← Set.range_comp] at h
  have hrows (i : N) : ∃ a ∈ 𝔞, ∃ z ∈ Submodule.span (MonoidAlgebra S G) (Set.range (ι ∘ y)),
      (B.map ι *ᵥ ι ∘ y) i = a + z * ι ρ₀ := by
    obtain ⟨a, ha, z, hz, h⟩ := hB i
    refine ⟨ι a, mapRingHom_mem_traceIdeal u S 𝒥 ha, ι z, hspan hz, ?_⟩
    rw [← RingHom.map_mulVec, h, map_add, map_mul]
  have htop : Submodule.span S {w : MonoidAlgebra S G |
      ∀ k, (ρ w).charpoly.coeff k ∈ (algebraMap S (Y → L)).range} = ⊤ :=
    eq_top_iff.2 fun w _ ↦ Submodule.subset_span (hchar w)
  -- Elaborating the polynomial of Ribet's method in one step is slow, so `hP` is stated first.
  have hP := AlgHom.exists_ribet_polynomial (R := S) (L := Y → L) (Λ := MonoidAlgebra S G)
    (N := N) ρ
  obtain ⟨P, hP0, -, htr, hδ⟩ := hP htop 𝔞 (fun _ ↦ mem_traceIdeal_of_map_eq_zero _) (ι ∘ y)
    (ι ρ₀) (B.map ι) hrows
  -- `f` is the trace of `ρ (ρ₁ P(ρ₀))`.
  obtain ⟨c, hc⟩ := htr (ι ρ₁)
  rw [Subalgebra.algebraMap_apply] at hc hP0
  refine ⟨c, c.property, fun w hw ↦ ?_, fun x hx ↦ ?_⟩
  · -- `det (u x w)` is the scalar `D` of `S` with `ρ (v * ι w) = D` for some `v`.
    obtain ⟨v, D, hD, hv, -⟩ :=
      AlgHom.exists_mul_eq_smul_one_of_charpoly_coeff_mem_range ρ (hchar (ι w))
    obtain ⟨a, ha, hDa⟩ := hδ (ι ρ₁) D ⟨v * ι w, Submodule.smul_mem _ v (hspan hw),
      by rw [map_mul, hv, Algebra.algebraMap_eq_smul_one]⟩
    have hdet : (fun x ↦ algebraMap O L (u x w).det) = algebraMap S (Y → L) D := by
      rw [← hD, familyLift_mapRingHom, det_familyAlgHom]
    rw [hdet, mul_comm, hc, hDa]
    exact trace_mem_of_mem_traceIdeal ha
  · rw [hc, trace_familyLift_mul_aeval_apply u S ρ₀ ρ₁ P hx, coeff_zero_eq_eval_zero, hP0,
      det_comp_map_familyLift_apply, map_mul]

/-- **Ribet's element for a matrix of tied rows, on block points.** In the setting of
`TauCeti.exists_ribet_element_of_tied_rows`, suppose that on a set `𝓧 ⊆ Y` every `u x` is, after
reindexing along `e : r ⊕ T ≃ σ`, the block sum of a representation `ψ x` and of characters `η t`,
that `ψ x ρ₁ = 0`, that `η t ρ₁` is `μ₀` for `t = t₀` and `0` otherwise, and that `η t₀ ρ₀ = 0`.
Then some `f ∈ S` has `f * (x ↦ det u x w) ∈ 𝒥` for every `w` in the left ideal spanned by `y`,
and `f x = μ₀ * det (ψ x B) * ∏ t, det (η t B)` for every `x ∈ 𝓧`, where `det (ψ x B)` is the
determinant of the block matrix `(ψ x (B i j))_{i,j}`. -/
theorem exists_ribet_element_of_tied_rows_of_blocks {r T : Type*} [Fintype r] [DecidableEq r]
    [Fintype T] [DecidableEq T] {e : r ⊕ T ≃ σ} (u : Y → MonoidAlgebra O G →ₐ[O] Matrix σ σ O)
    (S : Subalgebra O (Y → L))
    (hS : ∀ (g : G) (k : ℕ), (fun x ↦ algebraMap O L ((u x (single g 1)).charpoly.coeff k)) ∈ S)
    (𝒥 : Submodule S (Y → L)) (y : N → MonoidAlgebra O G) (ρ₀ ρ₁ : MonoidAlgebra O G)
    (B : Matrix N N (MonoidAlgebra O G))
    (hB : ∀ i, ∃ a ∈ Submodule.span (MonoidAlgebra O G)
        {w | ∀ g : G, (fun x ↦ algebraMap O L (u x (w * single g 1)).trace) ∈ 𝒥},
      ∃ z ∈ Submodule.span (MonoidAlgebra O G) (Set.range y), (B *ᵥ y) i = a + z * ρ₀)
    {𝓧 : Set Y} (ψ : 𝓧 → MonoidAlgebra O G →ₐ[O] Matrix r r O)
    (η : T → MonoidAlgebra O G →ₐ[O] O)
    (hu : ∀ (x : 𝓧) (w : MonoidAlgebra O G),
      u x w = reindex e e (fromBlocks (ψ x w) 0 0 (diagonal fun t ↦ η t w)))
    (hψ : ∀ x : 𝓧, ψ x ρ₁ = 0) (t₀ : T) {μ₀ : O} (hη₁ : ∀ t, η t ρ₁ = if t = t₀ then μ₀ else 0)
    (hη₀ : η t₀ ρ₀ = 0) :
    ∃ f ∈ S, (∀ w ∈ Submodule.span (MonoidAlgebra O G) (Set.range y),
        f * (fun x ↦ algebraMap O L (u x w).det) ∈ 𝒥) ∧
      ∀ x : 𝓧, f x = algebraMap O L
        (μ₀ * (comp N N r r O (B.map (ψ x))).det * ∏ t, (B.map (η t)).det) := by
  obtain ⟨f, hf, hJ, hval⟩ := exists_ribet_element_of_tied_rows u S hS 𝒥 y ρ₀ ρ₁ B hB
  refine ⟨f, hf, hJ, fun x ↦ ?_⟩
  have hη (t : T) : η t (ρ₁ * ρ₀) = 0 := by
    rw [map_mul, hη₁]
    split_ifs with ht
    · rw [ht, hη₀, mul_zero]
    · rw [zero_mul]
  have hzero : u x (ρ₁ * ρ₀) = 0 := by
    simp [hu, hη, hψ]
  have htrace : (u x ρ₁).trace = μ₀ := by
    rw [hu, trace_reindex_self]
    simp [hψ, hη₁, Matrix.trace_fromBlocks]
  rw [hval x hzero, htrace, det_comp_map_of_eq_reindex_fromBlocks_diagonal B (hu x), mul_comm,
    mul_assoc]

end TauCeti
