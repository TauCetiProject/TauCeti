/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import TauCeti.Algebra.Polynomial.Eval.IsUnit
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Cayley
public import TauCeti.Topology.Algebra.IsOpenUnits
public import TauCeti.Topology.Instances.Matrix

/-!
# Weak approximation for the unitary group of a hermitian form

Let `E` be a field with an involution, `J ∈ M_n(E)` an invertible hermitian matrix, and
`f : E →+* A` a ring homomorphism commuting with the involutions into a commutative topological ring
`A` with continuous involution, whose units are open with continuous inversion (`IsOpenUnits A`).
If `f` has dense range, then every matrix `M` over `A` preserving the form of `J`,
`star M * J.map f * M = J.map f`, is a limit of images under `f` of elements of the rational unitary
group `U(J)(E) = Matrix.unitaryGroupOf J` (`Matrix.mem_closure_range_map_unitaryGroupOf`), provided
`2 ≠ 0` in `E`, `E` has infinitely many unitary elements and `A` has finitely many maximal ideals.
Since the units of `M_n(A)` carry the topology of the matrices, this says that `U(J)(E)` is dense
in `U(J)(A)`, the unitary group of `J` read in `A`.

The typical `A` is a finite product of completions `E_w` of a number field `E`, at its infinite
places and at finitely many finite places, with the involution induced by the complex conjugation
of a CM field; then this is weak approximation for the unitary group of a hermitian space at those
places.

The proof is by the Cayley transform `c(X) = (1 - X) (1 + X)⁻¹`
(`Matrix.unitaryGroupOf.cayleyEquiv`), which identifies the elements `g` of the unitary group with
`1 + g` invertible with the matrices `X` skew for the form, `star X * J + J * X = 0`, with `1 + X`
invertible.

* The skew matrices over `A` are the image of the matrices over `A` under the projection
  `Z ↦ ½ (Z - J⁻¹ (star Z) J)`, which is defined over `E`. So the rational skew matrices are dense
  in the skew matrices over `A`, and since `c` is continuous where `1 + X` is invertible, every
  `g ∈ U(J)(A)` with `1 + g` invertible is a limit of rational unitary matrices
  (`Matrix.mem_closure_range_map_unitaryGroupOf_of_isUnit_one_add`).
* For a general `g`, the matrix `λ • 1 + g` is invertible for all but finitely many `λ ∈ E`,
  because `A` has finitely many maximal ideals
  (`Polynomial.Monic.finite_setOf_not_isUnit_eval`, applied to the characteristic polynomial).
  Choosing a unitary `λ` outside this finite set, `λ⁻¹ • g` falls in the previous case, and `g` is
  its translate by the rational unitary scalar `λ`
  (`Matrix.mem_closure_range_map_unitaryGroupOf`).

## Main results

* `Matrix.mem_closure_image_map_of_star_mul_add_mul_eq_zero`: the matrices over `E` skew for the
  form are dense in the matrices over `A` skew for the form.
* `Matrix.mem_closure_range_map_unitaryGroupOf_of_isUnit_one_add`: a matrix `g` over `A`
  preserving the form, with `1 + g` invertible, is a limit of images of rational unitary matrices.
* `Matrix.mem_closure_range_map_unitaryGroupOf`: every matrix over `A` preserving the form is a
  limit of images of rational unitary matrices.

## Provenance

The method, the Cayley transform onto the skew matrices followed by density of the rational
matrices and translation, is the one of `New.Space.weak_approximation` and `New.cayleyTransform`
(file `grh/src/Lib/Adelic/Unitary/WeakApproximation.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where it is
applied to a hermitian space with an adelic frame over a CM field. Here it is stated for an
abstract dense ring homomorphism, and the translation step uses a unitary scalar.

## References

* V. Platonov, A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), Chapter 7.
-/

public section

open Topology

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {E A : Type*} [Field E] [StarRing E] [CommRing A] [StarRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [ContinuousStar A] {f : E →+* A} {J : Matrix n n E}

/-- **The rational matrices skew for a hermitian form are dense.** Let `f : E →+* A` be a ring
homomorphism with dense range commuting with the involutions, `2 ≠ 0` in `E`, and `J` an invertible
hermitian matrix over `E`. Every matrix `X` over `A` skew for the form of `J`,
`star X * J.map f + J.map f * X = 0`, is a limit of images under `f` of matrices over `E` skew for
the form of `J`. -/
theorem mem_closure_image_map_of_star_mul_add_mul_eq_zero
    (hf : ∀ x, f (star x) = star (f x)) (hd : DenseRange f) (h2 : (2 : E) ≠ 0)
    (hJ : J.IsHermitian) (hJu : IsUnit J) {X : Matrix n n A}
    (hX : star X * J.map f + J.map f * X = 0) :
    X ∈ closure ((fun Y : Matrix n n E ↦ Y.map f) '' {Y | star Y * J + J * Y = 0}) := by
  have hdet : IsUnit J.det := (isUnit_iff_isUnit_det J).1 hJu
  have hJs : star J = J := by rw [star_eq_conjTranspose, hJ.eq]
  have hJis : star J⁻¹ = J⁻¹ := by rw [star_eq_conjTranspose, hJ.inv.eq]
  have hfs : ∀ Z : Matrix n n E, star (Z.map f) = (star Z).map f := fun Z ↦ by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_map f hf]
  -- The projection `Z ↦ ½ (Z - J⁻¹ (star Z) J)` onto the skew matrices, over `E` and over `A`.
  let PE : Matrix n n E → Matrix n n E := fun Z ↦ (2⁻¹ : E) • (Z - J⁻¹ * star Z * J)
  let P : Matrix n n A → Matrix n n A := fun W ↦ f 2⁻¹ • (W - J⁻¹.map f * star W * J.map f)
  have hPE : ∀ Z, star (PE Z) * J + J * PE Z = 0 := fun Z ↦ by
    simp only [PE, star_smul, star_sub, star_mul, star_star, hJs, hJis, star_inv₀, star_ofNat,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      nonsing_inv_mul _ hdet, Matrix.mul_one, mul_nonsing_inv_cancel_left _ _ hdet]
    rw [← smul_add, sub_add_sub_cancel', sub_self, smul_zero]
  have hPmap : ∀ Z, P (Z.map f) = (PE Z).map f := fun Z ↦ by
    simp only [P, PE, hfs, Matrix.map_smul' f _ _ (map_mul f)]
    simp only [← RingHom.mapMatrix_apply, map_sub, map_mul]
  -- The projection fixes the skew matrix `X`.
  have hPX : P X = X := by
    have hL : J⁻¹.map f * J.map f = 1 := by
      rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ f.map_zero f.map_one]
    have h : J⁻¹.map f * star X * J.map f = -X := by
      rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hX, Matrix.mul_neg, ← Matrix.mul_assoc,
        hL, Matrix.one_mul]
    simp only [P, h, sub_neg_eq_add, ← two_smul A X, smul_smul, ← map_ofNat f 2, ← map_mul,
      inv_mul_cancel₀ h2, map_one, one_smul]
  -- The rational matrices are dense, and `P` maps them to images of rational skew matrices.
  have hdM : Dense (Set.range fun Z : Matrix n n E ↦ Z.map f) := by
    refine (Dense.matrix (m := n) (n := n) hd).mono fun M hM ↦ ?_
    choose Z hZ using hM
    exact ⟨Matrix.of Z, ext fun i j ↦ hZ i j⟩
  have hPc : Continuous P := by fun_prop
  refine closure_mono ?_ (image_closure_subset_closure_image hPc ⟨X, hdM X, hPX⟩)
  rintro _ ⟨_, ⟨Z, rfl⟩, rfl⟩
  exact ⟨PE Z, hPE Z, (hPmap Z).symm⟩

/-- **Rational approximation in the domain of the Cayley transform.** Let `f : E →+* A` be a ring
homomorphism with dense range commuting with the involutions, `2 ≠ 0` in `E`, and `J` an invertible
hermitian matrix over `E`. A matrix `g` over `A` preserving the form of `J`, with `1 + g`
invertible, is a limit of images under `f` of elements of `unitaryGroupOf J`. -/
theorem mem_closure_range_map_unitaryGroupOf_of_isUnit_one_add [IsOpenUnits A]
    (hf : ∀ x, f (star x) = star (f x)) (hd : DenseRange f) (h2 : (2 : E) ≠ 0)
    (hJ : J.IsHermitian) (hJu : IsUnit J) {g : Matrix n n A}
    (hg : star g * J.map f * g = J.map f) (hg1 : IsUnit (1 + g)) :
    g ∈ closure (Set.range fun γ : unitaryGroupOf J ↦ ((γ : GL n E) : Matrix n n E).map f) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact subset_closure ⟨1, Subsingleton.elim _ _⟩
  have h2A : IsUnit (2 : Matrix n n A) := by
    simpa only [map_ofNat] using (Ne.isUnit h2).map ((algebraMap A (Matrix n n A)).comp f)
  -- The Cayley transform `X` of `g` is skew for the form, `1 + X` is invertible and `c(X) = g`.
  set X := TauCeti.cayleyCoord 1 g
  have hX1 : IsUnit (1 + X) := TauCeti.isUnit_one_add_cayleyCoord_one h2A g
  have hXX : TauCeti.cayleyCoord 1 X = g := TauCeti.cayleyCoord_one_cayleyCoord_one h2A hg1
  -- `X` is a limit of rational skew matrices `Y` with `1 + Y` invertible.
  have hO : IsOpen {W : Matrix n n A | IsUnit (1 + W)} :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_range.preimage (continuous_const.add continuous_id)
  have hXT := hO.inter_closure ⟨hX1, mem_closure_image_map_of_star_mul_add_mul_eq_zero hf hd h2
    hJ hJu (star_cayleyCoord_one_mul_add_mul_cayleyCoord_one hg)⟩
  -- The Cayley transform is continuous at `X`, so `g = c(X)` is a limit of the `c(Y)`.
  have hc : ContinuousAt (TauCeti.cayleyCoord (1 : Matrix n n A)) X := by
    have hinv : ContinuousAt Ring.inverse (1 + X) :=
      IsOpenUnits.continuousAt_ringInverse hX1.unit
    have hden : ContinuousAt (fun W : Matrix n n A ↦ 1 + W) X :=
      (continuous_const.add continuous_id).continuousAt
    rw [TauCeti.cayleyCoord_eq_fun]
    exact (continuous_const.sub continuous_id).continuousAt.mul
      (ContinuousAt.comp (g := Ring.inverse) hinv hden)
  have hgc := hc.continuousWithinAt.mem_closure_image hXT
  rw [hXX] at hgc
  refine closure_mono ?_ hgc
  rintro _ ⟨_, ⟨hY1A, Y, hY, rfl⟩, rfl⟩
  -- `Y` is skew with `1 + Y` invertible, so its Cayley transform is a rational unitary matrix.
  have hY1 : IsUnit (1 + Y) := by
    rw [isUnit_iff_isUnit_det, ← isUnit_map_iff f, RingHom.map_det, map_add, map_one,
      RingHom.mapMatrix_apply, ← isUnit_iff_isUnit_det]
    exact hY1A
  refine ⟨unitaryGroupOf.ofMatrix hJu _ (star_cayleyCoord_one_mul_mul_cayleyCoord_one hY hY1), ?_⟩
  simp only [unitaryGroupOf.val_ofMatrix]
  rw [← RingHom.mapMatrix_apply,
    TauCeti.map_cayleyCoord_of_isUnit _ hY1, map_one, RingHom.mapMatrix_apply]

/-- **Weak approximation for the unitary group of a hermitian form, at the level of matrices.**
Let `f : E →+* A` be a ring homomorphism with dense range commuting with the involutions, where
`2 ≠ 0` in `E`, `E` has infinitely many unitary elements and `A` has finitely many maximal ideals,
and let `J` be an invertible hermitian matrix over `E`. Every matrix `M` over `A` preserving the
form of `J` is a limit of images under `f` of elements of `unitaryGroupOf J`. -/
theorem mem_closure_range_map_unitaryGroupOf [IsOpenUnits A] [Finite (MaximalSpectrum A)]
    [Infinite (unitary E)] (hf : ∀ x, f (star x) = star (f x)) (hd : DenseRange f)
    (h2 : (2 : E) ≠ 0) (hJ : J.IsHermitian) (hJu : IsUnit J) {M : Matrix n n A}
    (hM : star M * J.map f * M = J.map f) :
    M ∈ closure (Set.range fun γ : unitaryGroupOf J ↦ ((γ : GL n E) : Matrix n n E).map f) := by
  set S := Set.range fun γ : unitaryGroupOf J ↦ ((γ : GL n E) : Matrix n n E).map f
  -- `scalar u + M` is invertible for all but finitely many `u`; pick a unitary `u` outside them.
  have hfin : {u : unitary E | ¬IsUnit (scalar n (f u) + M)}.Finite := by
    refine (((Matrix.charpoly_monic (-M)).finite_setOf_not_isUnit_eval f).preimage
      Subtype.val_injective.injOn).subset fun u hu ↦ ?_
    simpa [isUnit_iff_isUnit_det, eval_charpoly] using hu
  obtain ⟨u, hu⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] at hu
  have hfu : f (star (u : E)) * f u = 1 := by rw [← map_mul, Unitary.coe_star_mul_self, map_one]
  have hfu' : f u * f (star (u : E)) = 1 := by rw [mul_comm, hfu]
  -- `g = (star u) • M` preserves the form and has `1 + g = (star u) • (scalar u + M)` invertible.
  set g := f (star (u : E)) • M
  have hg : star g * J.map f * g = J.map f := by
    simp only [g, star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM, ← hf, star_star,
      hfu, one_smul]
  have hg1 : IsUnit (1 + g) := by
    have h : 1 + g = scalar n (f (star (u : E))) * (scalar n (f u) + M) := by
      rw [Matrix.mul_add, ← map_mul, hfu, map_one, scalar_apply, ← smul_eq_diagonal_mul]
    rw [h]
    exact ((IsUnit.of_mul_eq_one _ hfu).map (scalar n)).mul hu
  have hgS := mem_closure_range_map_unitaryGroupOf_of_isUnit_one_add hf hd h2 hJ hJu hg hg1
  -- `M = u • g`, and multiplication by the rational unitary scalar `u` preserves `S`.
  have hMg : M = f u • g := by rw [smul_smul, hfu', one_smul]
  have hS : (f u • ·) '' S ⊆ S := by
    rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
    refine ⟨unitaryGroupOf.scalarHom J u * γ, ?_⟩
    simp only [Subgroup.coe_mul, Units.val_mul, unitaryGroupOf.val_scalarHom, scalar_apply,
      ← smul_eq_diagonal_mul, Matrix.map_smul' f _ _ (map_mul f)]
  rw [hMg]
  exact closure_mono hS (image_closure_subset_closure_image (continuous_const_smul _) ⟨g, hgS, rfl⟩)

end Matrix
