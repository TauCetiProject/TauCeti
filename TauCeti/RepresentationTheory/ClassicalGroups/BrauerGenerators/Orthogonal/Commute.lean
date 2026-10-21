/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.BrauerGenerators.Orthogonal.Action

/-!
# The Brauer action commutes with the orthogonal group

The Brauer algebra `B_k(n)` acts on the tensor power `V^{⊗k}` of `V = Rⁿ` through the standard
symmetric form (`TauCeti.brauerActionOrth`), and the orthogonal group of that form acts on
`V^{⊗k}` diagonally. This file proves, over every commutative ring, that the two actions commute,
so that the image of the Brauer algebra lies in the commutant of the orthogonal group. This is
one inclusion of Brauer's orthogonal Schur-Weyl duality. Over `ℂ` the image is the whole
commutant, which is the first fundamental theorem of invariant theory for the orthogonal group;
that is not part of this file.

The commutation is proved for every Brauer diagram at once, rather than generator by generator.
Read the matrix of a diagram `D` in the monomial basis as a function of the labellings
`x : Fin k ⊕ Fin k → ι` of its `2k` boundary points: it is the indicator of the labellings
constant on the arcs of `D`, a product over the arcs of `D` of copies of the copairing
`∑ c, e_c ⊗ e_c`. A matrix `A` with `A * Aᵀ = 1` fixes the copairing, so applying `A` at every
boundary point fixes this indicator (`TauCeti.BrauerDiagram.sum_prod_mul_ite_isConstantOnArcs`).
Splitting the boundary into its bottom and top halves, this says `T * M * Tᵀ = M` for the matrix
`M` of `D` and the matrix `T` of the diagonal action of `A`, and `Tᵀ * T = 1` turns it into
`T * M = M * T`.

## Main results

* `TauCeti.BrauerDiagram.sum_prod_mul_ite_isConstantOnArcs`: the indicator of the labellings
  constant on the arcs of a Brauer diagram is invariant under a matrix `A` with `A * Aᵀ = 1`
  applied at every boundary point.
* `TauCeti.commute_brauerActionOrth_piTensorProductMap`: every element of the Brauer algebra acts
  on `(Rⁿ)^{⊗k}` commuting with the diagonal action of a matrix `A` with `Aᵀ * A = 1`.
* `TauCeti.commute_brauerActionOrth_tensorPower`: the Brauer action commutes with the diagonal
  action of the orthogonal group.
* `TauCeti.range_brauerActionOrth_le_centralizer`: the image of the Brauer algebra lies in the
  centralizer of the image of the orthogonal group.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

open Matrix

namespace TauCeti

universe u

namespace BrauerDiagram

variable {R : Type u} [CommSemiring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

/-- **The arc indicator of a Brauer diagram is orthogonally invariant.** Applying a matrix `A`
with `A * Aᵀ = 1` at every boundary point of `D` fixes the indicator of the labellings constant
on the arcs of `D`. Read as a tensor on the `2k` boundary points, the indicator is a product over
the arcs of copies of the copairing `∑ c, e_c ⊗ e_c`, which `A ⊗ A` fixes. -/
theorem sum_prod_mul_ite_isConstantOnArcs (D : BrauerDiagram k) {A : Matrix ι ι R}
    (hA : A * Aᵀ = 1) (x : Fin k ⊕ Fin k → ι) :
    ∑ y : Fin k ⊕ Fin k → ι, (∏ p, A (x p) (y p)) * (if D.IsConstantOnArcs y then 1 else 0) =
      if D.IsConstantOnArcs x then 1 else 0 := by
  -- Pick a set `S` containing exactly one end of every arc. A labelling constant on arcs is a
  -- free labelling of `S`, and along it the product over the boundary is a product over the arcs.
  -- The sum over labellings of `S` then factors over the arcs, each factor being an entry of
  -- `A * Aᵀ = 1`, and the product of these entries is the arc indicator of `x`.
  classical
  set σ := D.val
  have hσσ : ∀ p, σ (σ p) = p := D.apply_apply
  -- Choose one end of every arc: the end that comes first along `finSumFinEquiv`.
  let e : Fin k ⊕ Fin k → ℕ := fun p => (finSumFinEquiv p : ℕ)
  have he : Function.Injective e := fun p q h => finSumFinEquiv.injective (Fin.ext h)
  let S : Finset (Fin k ⊕ Fin k) := Finset.univ.filter fun p => e p < e (σ p)
  have hS : ∀ p, p ∉ S ↔ σ p ∈ S := by
    intro p
    have hne : e p ≠ e (σ p) := fun h => D.apply_ne p (he h).symm
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt, hσσ]
    omega
  -- A labelling constant on arcs is determined by its labels on `S`, freely chosen.
  let Φ : (S → ι) → Fin k ⊕ Fin k → ι := fun z p =>
    if h : p ∈ S then z ⟨p, h⟩ else z ⟨σ p, (hS p).1 h⟩
  have hΦS : ∀ z (s : S), Φ z s = z s := fun z s => by simp [Φ]
  have hΦσ : ∀ z (s : S), Φ z (σ s) = z s := fun z s => by
    have h : σ s ∉ S := fun h => (hS s).2 h s.2
    simp only [Φ, h, dite_false]
    congr 1
    exact Subtype.ext (hσσ s)
  have hΦinj : Function.Injective Φ := fun z z' h => funext fun s => by
    rw [← hΦS z s, ← hΦS z' s, h]
  have himage : Finset.univ.filter (fun y => D.IsConstantOnArcs y) = Finset.univ.image Φ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      isConstantOnArcs_def]
    refine ⟨fun hy => ⟨fun s => y s, funext fun p => ?_⟩, ?_⟩
    · by_cases hp : p ∈ S
      · simp [Φ, hp]
      · simp only [Φ, hp, dite_false]
        exact hy p
    · rintro ⟨z, rfl⟩ p
      by_cases hp : p ∈ S
      · exact (hΦσ z ⟨p, hp⟩).trans (hΦS z ⟨p, hp⟩).symm
      · have := hΦσ z ⟨σ p, (hS p).1 hp⟩
        simp only [hσσ] at this
        rw [this, ← hΦS z ⟨σ p, (hS p).1 hp⟩]
  -- Along such a labelling, the product over the boundary is a product over the arcs.
  have hprod : ∀ z : S → ι, ∏ p, A (x p) (Φ z p) =
      ∏ s : S, (A (x s) (z s) * A (x (σ s)) (z s)) := by
    intro z
    rw [← Finset.prod_mul_prod_compl S]
    have hcompl : ∏ p ∈ Sᶜ, A (x p) (Φ z p) = ∏ p ∈ S, A (x (σ p)) (Φ z (σ p)) :=
      Finset.prod_nbij' σ σ (fun p hp => (hS p).1 (Finset.mem_compl.1 hp))
        (fun p hp => Finset.mem_compl.2 fun h => (hS (σ p)).2 (by rwa [hσσ]) h)
        (fun p _ => hσσ p) (fun p _ => hσσ p) (fun p _ => by rw [hσσ])
    rw [hcompl, ← Finset.prod_mul_distrib, ← Finset.prod_coe_sort]
    exact Finset.prod_congr rfl fun s _ => by rw [hΦS, hΦσ]
  -- Summing over the label of one arc meets the identity `A * Aᵀ = 1`.
  have hpair : ∀ s : S, ∑ c, A (x s) c * A (x (σ s)) c =
      if x (σ s) = x s then 1 else 0 := by
    intro s
    have := congrFun (congrFun hA (x s)) (x (σ s))
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    rw [this]
    exact if_congr eq_comm rfl rfl
  calc ∑ y, (∏ p, A (x p) (y p)) * (if D.IsConstantOnArcs y then 1 else 0)
      = ∑ y ∈ Finset.univ.filter (fun y => D.IsConstantOnArcs y), ∏ p, A (x p) (y p) := by
        rw [Finset.sum_filter]
        simp only [mul_ite, mul_one, mul_zero]
    _ = ∑ z : S → ι, ∏ s : S, (A (x s) (z s) * A (x (σ s)) (z s)) := by
        rw [himage, Finset.sum_image fun z _ z' _ h => hΦinj h]
        exact Finset.sum_congr rfl fun z _ => hprod z
    _ = ∏ s : S, ∑ c, A (x s) c * A (x (σ s)) c :=
        (Fintype.prod_sum fun (s : S) c => A (x s) c * A (x (σ s)) c).symm
    _ = ∏ s : S, if x (σ s) = x s then 1 else 0 := Finset.prod_congr rfl fun s _ => hpair s
    _ = if D.IsConstantOnArcs x then 1 else 0 := by
        rw [Fintype.prod_boole]
        refine if_congr ?_ rfl rfl
        rw [isConstantOnArcs_def]
        refine ⟨fun h p => ?_, fun h s => h s⟩
        by_cases hp : p ∈ S
        · exact h ⟨p, hp⟩
        · have := h ⟨σ p, (hS p).1 hp⟩
          simp only [hσσ] at this
          exact this.symm

end BrauerDiagram

section CommSemiring

variable {R : Type u} [CommSemiring R] {n k : ℕ}

/-- The matrix of the diagonal action of `A` on `(Rⁿ)^{⊗k}` in the monomial basis. -/
private theorem toMatrix_piTensorProductMap (A : Matrix (Fin n) (Fin n) R) :
    LinearMap.toMatrix (tensorPowerBasis R n k) (tensorPowerBasis R n k)
        (PiTensorProduct.map fun _ : Fin k => Matrix.mulVecLin A) =
      Matrix.of fun v u => ∏ i, A (v i) (u i) := by
  ext v u
  rw [LinearMap.toMatrix_apply, tensorPowerBasis_def, Basis.piTensorProduct_apply,
    PiTensorProduct.map_tprod, Basis.piTensorProduct_repr_tprod_apply]
  simp

/-- **The Brauer action commutes with the diagonal action of an orthogonal matrix.** Every element
of the Brauer algebra `B_k(n)` acts on `(Rⁿ)^{⊗k}` commuting with `A ⊗ ⋯ ⊗ A` for every matrix `A`
with `Aᵀ * A = 1`. -/
theorem commute_brauerActionOrth_piTensorProductMap {A : Matrix (Fin n) (Fin n) R}
    (hA : Aᵀ * A = 1) (b : BrauerAlgebra R (n : R) k) :
    Commute (brauerActionOrth R n k b)
      (PiTensorProduct.map fun _ : Fin k => Matrix.mulVecLin A) := by
  rw [← (BrauerAlgebra.basis R (n : R) k).sum_repr b]
  simp only [map_sum, map_smul, BrauerAlgebra.basis_apply]
  refine Commute.sum_left _ _ _ fun D _ => Commute.smul_left ?_ _
  set T : Matrix (Fin k → Fin n) (Fin k → Fin n) R := Matrix.of fun v u => ∏ i, A (v i) (u i)
  set M := D.orthogonalActionMatrix R (Fin n)
  have hconj : T * M * Tᵀ = M := by
    ext v u
    have key := D.sum_prod_mul_ite_isConstantOnArcs (mul_eq_one_comm.mp hA) (Sum.elim u v)
    -- Split a labelling of the boundary into its bottom and top labellings.
    have helim : ∀ w w' : Fin k → Fin n,
        (Equiv.sumArrowEquivProdArrow _ _ _).symm (w, w') = Sum.elim w w' := fun w w' => by
      funext p
      rcases p with i | i <;> simp
    rw [← (Equiv.sumArrowEquivProdArrow _ _ _).symm.sum_comp, Fintype.sum_prod_type] at key
    simp only [helim, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr] at key
    simp only [T, M, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply,
      BrauerDiagram.orthogonalActionMatrix_apply, Finset.sum_mul]
    rw [← key]
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
  have horth : Tᵀ * T = 1 := by
    ext v u
    simp only [T, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum fun i c => A c (v i) * A c (u i)]
    have hcol : ∀ i, ∑ c, A c (v i) * A c (u i) = (1 : Matrix (Fin n) (Fin n) R) (v i) (u i) :=
      fun i => by simp [← hA, Matrix.mul_apply]
    simp only [hcol, Matrix.one_apply, Fintype.prod_boole, funext_iff]
    -- The two sides decide `∀ i, v i = u i` through different instances.
    congr 1
  have hcomm : M * T = T * M := by
    calc M * T = T * M * Tᵀ * T := by rw [hconj]
      _ = T * M := by rw [Matrix.mul_assoc (T * M), horth, Matrix.mul_one]
  apply (LinearMap.toMatrix (tensorPowerBasis R n k) (tensorPowerBasis R n k)).injective
  rw [LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, brauerActionOrth_of,
    LinearMap.toMatrix_toLin, toMatrix_piTensorProductMap]
  exact hcomm

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R] {n k : ℕ}

/-- **The Brauer action commutes with the orthogonal group.** Every element of the Brauer algebra
`B_k(n)` acts on `(Rⁿ)^{⊗k}` by an endomorphism commuting with the diagonal action of every element
of the orthogonal group of the standard symmetric form. -/
theorem commute_brauerActionOrth_tensorPower (g : Matrix.orthogonalGroup (Fin n) R)
    (b : BrauerAlgebra R (n : R) k) :
    Commute (brauerActionOrth R n k b) ((stdOrthogonalRep R n).tensorPower k g) := by
  rw [Representation.tensorPower_apply]
  simpa only [stdOrthogonalRep_apply] using
    commute_brauerActionOrth_piTensorProductMap
      ((Matrix.mem_orthogonalGroup_iff' (Fin n) R).mp g.prop) b

/-- **The image of the Brauer algebra centralizes the orthogonal group**: it lies in the
centralizer of the image of the orthogonal group in the endomorphisms of `(Rⁿ)^{⊗k}`. -/
theorem range_brauerActionOrth_le_centralizer :
    (brauerActionOrth R n k).range ≤
      Subalgebra.centralizer R (Set.range ((stdOrthogonalRep R n).tensorPower k)) := by
  rintro _ ⟨b, rfl⟩
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨g, rfl⟩
  exact (commute_brauerActionOrth_tensorPower g b).symm.eq

end CommRing

end TauCeti
