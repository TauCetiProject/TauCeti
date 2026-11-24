/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The symplectic similitude group as a subgroup of the general linear group

For a commutative ring `R` and a finite index type `l`, the **symplectic similitude group**
`GSp(l ⊕ l, R)` consists of the invertible matrices `γ` that preserve Mathlib's standard
alternating form `Matrix.J` up to a unit scalar, `γ J γᵀ = c J` with `c ∈ Rˣ`. When `l` is
nonempty the scalar `c = c(γ)` is determined by `γ`, because `J` has an entry equal to `1`, and
`γ ↦ c(γ)` is a homomorphism `GSp(l ⊕ l, R) →* Rˣ`, the **similitude multiplier**. Its kernel is
the symplectic group `TauCeti.GLSymplectic`.

This is the concrete group of matrices in which the congruence level subgroups of Siegel modular
varieties live: over `ℤ_p` these are cut out of `GSp(l ⊕ l, ℤ_p)` by conditions on the reduction
modulo `pᵐ` (the restriction `TauCeti.GLSymplecticSimilitude.map` of the entrywise map
`Matrix.GeneralLinearGroup.map`) and on the multiplier. In genus one, `l = Unit`, every invertible
matrix is a similitude and `c = det` (`TauCeti.GLSymplecticSimilitude.eq_top_of_unique` and
`TauCeti.GLSymplecticSimilitude.multiplier_eq_det`), so `GSp₂ = GL₂`.

The defining condition can equivalently be written `γᵀ J γ = c J`
(`Matrix.mul_J_mul_transpose_eq_smul_iff`); the sign convention of the alternating form does not
matter, since replacing `J` by `-J` does not change the condition.

## Main definitions

* `TauCeti.GLSymplecticSimilitude l R`: the symplectic similitudes, a subgroup of `GL (l ⊕ l) R`.
* `TauCeti.GLSymplecticSimilitude.multiplier`: the similitude multiplier `c : GSp →* Rˣ`, for
  nonempty `l`.
* `TauCeti.GLSymplecticSimilitude.map`: the homomorphism induced by a ring homomorphism.

## Main results

* `Matrix.mul_J_mul_transpose_eq_smul_iff`: for a unit `c`, `M J Mᵀ = c J ↔ Mᵀ J M = c J`.
* `TauCeti.GLSymplecticSimilitude.mul_J_mul_transpose` and `transpose_mul_J_mul`: the form
  identities `γ J γᵀ = c(γ) J` and `γᵀ J γ = c(γ) J`, with `multiplier_eq_iff` characterising
  the multiplier.
* `TauCeti.GLSymplecticSimilitude.mem_ker_multiplier_iff` and `GLSymplectic_le`: the kernel of
  the multiplier is the symplectic group.
* `TauCeti.GLSymplecticSimilitude.coe_inv_eq_smul_fromBlocks` and
  `toBlocks₂₂_mul_transpose_sub`: in `l × l` blocks `γ = (A B; C D)`, the inverse is
  `c(γ)⁻¹ (Dᵀ -Bᵀ; -Cᵀ Aᵀ)` and `D Aᵀ - C Bᵀ = c(γ) 1`; the first rests on
  `Matrix.neg_J_mul_transpose_mul_J`, the block form of the symplectic adjoint.
* `TauCeti.GLSymplecticSimilitude.multiplier_map`: the multiplier commutes with change of rings.
* `Matrix.mul_J_mul_transpose_eq_det_smul`: in genus one `M J Mᵀ = det M • J`
  for every matrix `M`, whence `eq_top_of_unique` and `multiplier_eq_det`.

## References

* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. (2)
  182 (2015), §3.1, where `GSp_2g` and its level subgroups are introduced.
-/

public section

open Matrix

namespace Matrix

variable {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]

omit [Fintype l] in
/-- Over a nonempty index type, a scalar multiple of `Matrix.J` determines the scalar, since `J`
has an entry equal to `1`. -/
theorem smul_J_injective [Nonempty l] : Function.Injective fun c : R => c • J l R := by
  intro c d h
  have := congrFun (congrFun h (Sum.inr (Classical.arbitrary l))) (Sum.inl (Classical.arbitrary l))
  simpa [J] using this

/-- One direction of `Matrix.mul_J_mul_transpose_eq_smul_iff`. -/
private theorem transpose_mul_J_mul_eq_smul_of {M : Matrix (l ⊕ l) (l ⊕ l) R} {c : R}
    (hc : IsUnit c) (h : M * J l R * Mᵀ = c • J l R) : Mᵀ * J l R * M = c • J l R := by
  obtain ⟨u, rfl⟩ := hc
  -- `N = c⁻¹ • (J Mᵀ (-J))` is a right inverse of `M`, hence also a left inverse.
  have hMN : M * ((↑u⁻¹ : R) • (J l R * Mᵀ * -J l R)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.smul_mul,
      J_mul_neg_J, smul_smul, Units.inv_mul, one_smul]
  have hNM := mul_eq_one_comm.mp hMN
  rw [Matrix.smul_mul] at hNM
  have hJ : J l R * (Mᵀ * -J l R * M) = (u : R) • 1 := by
    have := congrArg ((u : R) • ·) hNM
    simpa [smul_smul, Matrix.mul_assoc] using this
  calc Mᵀ * J l R * M = -(-J l R * J l R * (Mᵀ * -J l R * M)) := by
        rw [neg_J_mul_J]; noncomm_ring
    _ = (u : R) • J l R := by
        rw [Matrix.mul_assoc, hJ, Matrix.mul_smul, Matrix.mul_one, smul_neg, neg_neg]

/-- **The two forms of the similitude condition agree**: for a unit `c`, `M J Mᵀ = c J` exactly
when `Mᵀ J M = c J`. For `c = 1` this is Mathlib's `SymplecticGroup.mem_iff'`. -/
theorem mul_J_mul_transpose_eq_smul_iff {M : Matrix (l ⊕ l) (l ⊕ l) R} {c : R} (hc : IsUnit c) :
    M * J l R * Mᵀ = c • J l R ↔ Mᵀ * J l R * M = c • J l R :=
  ⟨transpose_mul_J_mul_eq_smul_of hc, fun h => by
    simpa using transpose_mul_J_mul_eq_smul_of hc (M := Mᵀ) (by simpa using h)⟩

/-- The symplectic adjoint `-(J Mᵀ J)` of a matrix `M = (A B; C D)` is `(Dᵀ -Bᵀ; -Cᵀ Aᵀ)`. -/
theorem neg_J_mul_transpose_mul_J (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    -(J l R * Mᵀ * J l R) = fromBlocks M.toBlocks₂₂ᵀ (-M.toBlocks₁₂ᵀ) (-M.toBlocks₂₁ᵀ)
      M.toBlocks₁₁ᵀ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_neg]

/-- **Genus one**: if `l` has exactly one element, every matrix `M` indexed by `l ⊕ l` satisfies
`M J Mᵀ = det M • J`; in classical notation `γ J γᵀ = (ad - bc) J` for `γ = (a b; c d)`. -/
theorem mul_J_mul_transpose_eq_det_smul [Unique l]
    (M : Matrix (l ⊕ l) (l ⊕ l) R) : M * J l R * Mᵀ = M.det • J l R := by
  let e : l ⊕ l ≃ Fin 2 := (Equiv.sumCongr (Equiv.ofUnique l (Fin 1))
    (Equiv.ofUnique l (Fin 1))).trans finSumFinEquiv
  have hdet : M.det = M (Sum.inl default) (Sum.inl default) * M (Sum.inr default) (Sum.inr default)
      - M (Sum.inl default) (Sum.inr default) * M (Sum.inr default) (Sum.inl default) := by
    rw [← det_reindex_self e, det_fin_two]
    simp [e, Fin.addCases, finSumFinEquiv]
  ext (i | i) (j | j) <;>
    simp [hdet, J, Matrix.mul_apply, Fintype.sum_sum_type, Unique.eq_default i,
      Unique.eq_default j] <;> ring

end Matrix

namespace TauCeti

/-- Similitude factors multiply: if `A J Aᵀ = c J` and `B J Bᵀ = d J` then
`(A B) J (A B)ᵀ = (c d) J`. -/
private theorem mul_mul_J_mul_transpose {l : Type*} [DecidableEq l] [Fintype l] {R : Type*}
    [CommRing R] {A B : Matrix (l ⊕ l) (l ⊕ l) R} {c d : R} (hA : A * J l R * Aᵀ = c • J l R)
    (hB : B * J l R * Bᵀ = d • J l R) : A * B * J l R * (A * B)ᵀ = (c * d) • J l R := by
  calc A * B * J l R * (A * B)ᵀ = A * (B * J l R * Bᵀ) * Aᵀ := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = (c * d) • J l R := by
        rw [hB, Matrix.mul_smul, Matrix.smul_mul, hA, smul_smul, mul_comm]

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type*) [CommRing R]

/-- **The symplectic similitude group** `GSp(l ⊕ l, R)` as a subgroup of `GL (l ⊕ l) R`: the
invertible matrices `γ` with `γ J γᵀ = c J` for some unit `c`. -/
def GLSymplecticSimilitude : Subgroup (GL (l ⊕ l) R) where
  carrier := {M | ∃ c : Rˣ, (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
    (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (c : R) • J l R}
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, by rw [Units.val_mul, Units.val_mul, mul_mul_J_mul_transpose hc hd]⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    have hl : ((a⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) *
        (a : Matrix (l ⊕ l) (l ⊕ l) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hr : (a : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ *
        ((a⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = 1 := by
      rw [← transpose_mul, hl, transpose_one]
    calc ((a⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
          ((a⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ =
          ((c⁻¹ : Rˣ) : R) • (((a⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) *
            ((c : R) • J l R) * ((a⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Units.inv_mul, one_smul]
      _ = ((c⁻¹ : Rˣ) : R) • J l R := by
          rw [← hc]
          simp only [← Matrix.mul_assoc, hl, Matrix.one_mul]
          rw [Matrix.mul_assoc, hr, Matrix.mul_one]

namespace GLSymplecticSimilitude

variable {l R}

/-- Membership in the similitude group: `γ J γᵀ = c J` for some unit `c`. -/
theorem mem_iff {M : GL (l ⊕ l) R} :
    M ∈ GLSymplecticSimilitude l R ↔ ∃ c : Rˣ, (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (c : R) • J l R :=
  Iff.rfl

/-- Membership in the similitude group, in the transposed form `γᵀ J γ = c J`. -/
theorem mem_iff' {M : GL (l ⊕ l) R} :
    M ∈ GLSymplecticSimilitude l R ↔ ∃ c : Rˣ, (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R *
      (M : Matrix (l ⊕ l) (l ⊕ l) R) = (c : R) • J l R :=
  exists_congr fun c => mul_J_mul_transpose_eq_smul_iff c.isUnit

/-- Every symplectic matrix is a symplectic similitude, with multiplier `1`. -/
theorem GLSymplectic_le : GLSymplectic l R ≤ GLSymplecticSimilitude l R :=
  fun M hM => ⟨1, by rw [Units.val_one, one_smul, ← GLSymplectic.mem_iff]; exact hM⟩

section Multiplier

variable [Nonempty l]

/-- Over a nonempty index type, the scalar in the similitude condition is unique. -/
private theorem unit_eq_of_smul_J {M : GL (l ⊕ l) R} {c d : Rˣ}
    (hc : (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (c : R) • J l R)
    (hd : (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (d : R) • J l R) : c = d :=
  Units.ext (smul_J_injective (hc.symm.trans hd))

variable (l R) in
/-- **The similitude multiplier** `c : GSp(l ⊕ l, R) →* Rˣ`, the unique unit with
`γ J γᵀ = c(γ) J`. It is well defined because `l` is nonempty. -/
noncomputable def multiplier : GLSymplecticSimilitude l R →* Rˣ where
  toFun M := M.property.choose
  map_one' := unit_eq_of_smul_J (1 : GLSymplecticSimilitude l R).property.choose_spec (by simp)
  map_mul' M N := by
    refine unit_eq_of_smul_J (M * N).property.choose_spec ?_
    have hc := M.property.choose_spec
    have hd := N.property.choose_spec
    generalize M.property.choose = c at hc ⊢
    generalize N.property.choose = d at hd ⊢
    rw [Subgroup.coe_mul, Units.val_mul, Units.val_mul, mul_mul_J_mul_transpose hc hd]

/-- **The defining form identity** `γ J γᵀ = c(γ) J`. -/
theorem mul_J_mul_transpose (M : GLSymplecticSimilitude l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ =
      (multiplier l R M : R) • J l R :=
  M.property.choose_spec

/-- **The transposed form identity** `γᵀ J γ = c(γ) J`. -/
theorem transpose_mul_J_mul (M : GLSymplecticSimilitude l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R *
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      (multiplier l R M : R) • J l R :=
  (mul_J_mul_transpose_eq_smul_iff (Units.isUnit _)).1 (mul_J_mul_transpose M)

/-- The multiplier is the unique unit `c` with `γ J γᵀ = c J`. -/
theorem multiplier_eq_iff {M : GLSymplecticSimilitude l R} {c : Rˣ} :
    multiplier l R M = c ↔ ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (c : R) • J l R :=
  ⟨fun h => h ▸ mul_J_mul_transpose M, fun h => unit_eq_of_smul_J (mul_J_mul_transpose M) h⟩

/-- The multiplier is the `(inr i, inl i)` entry of `γ J γᵀ`. -/
theorem coe_multiplier_eq_apply (M : GLSymplecticSimilitude l R) (i : l) :
    (multiplier l R M : R) = (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ) (Sum.inr i) (Sum.inl i) := by
  rw [mul_J_mul_transpose]
  simp [J]

/-- **The kernel of the multiplier is the symplectic group.** -/
theorem mem_ker_multiplier_iff {M : GLSymplecticSimilitude l R} :
    M ∈ (multiplier l R).ker ↔ (M : GL (l ⊕ l) R) ∈ GLSymplectic l R := by
  rw [MonoidHom.mem_ker, multiplier_eq_iff, Units.val_one, one_smul, GLSymplectic.mem_iff]

/-- A symplectic matrix has multiplier `1`. -/
theorem multiplier_eq_one_of_mem {M : GLSymplecticSimilitude l R}
    (hM : (M : GL (l ⊕ l) R) ∈ GLSymplectic l R) : multiplier l R M = 1 :=
  mem_ker_multiplier_iff.2 hM

/-- **The inverse of a symplectic similitude** `γ = (A B; C D)` is
`c(γ)⁻¹ (Dᵀ -Bᵀ; -Cᵀ Aᵀ)`. -/
theorem coe_inv_eq_smul_fromBlocks (M : GLSymplecticSimilitude l R) :
    (((M⁻¹ : GLSymplecticSimilitude l R) : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      (((multiplier l R M)⁻¹ : Rˣ) : R) •
        fromBlocks ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ᵀ
          (-((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₂ᵀ)
          (-((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ᵀ)
          ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ᵀ := by
  rw [← neg_J_mul_transpose_mul_J]
  set X := (((multiplier l R M)⁻¹ : Rˣ) : R) •
    -(J l R * ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R)
  have hMX : ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X = 1 := by
    simp only [X, Matrix.mul_smul, Matrix.mul_neg, ← Matrix.mul_assoc, mul_J_mul_transpose,
      Matrix.smul_mul, J_squared, smul_neg, neg_neg, smul_smul, Units.inv_mul, one_smul]
  calc (((M⁻¹ : GLSymplecticSimilitude l R) : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
        (((M⁻¹ : GLSymplecticSimilitude l R) : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) *
          (((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * X) := by rw [hMX, Matrix.mul_one]
    _ = X := by
        rw [← Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
        simp

/-- **A block identity for symplectic similitudes**: for `γ = (A B; C D)`,
`D Aᵀ - C Bᵀ = c(γ) 1`. -/
theorem toBlocks₂₂_mul_transpose_sub (M : GLSymplecticSimilitude l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₂ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₁ᵀ -
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₂₁ *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).toBlocks₁₂ᵀ =
      (multiplier l R M : R) • 1 := by
  have h := congrArg toBlocks₂₁ (mul_J_mul_transpose M)
  conv_lhs at h => rw [← fromBlocks_toBlocks ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)]
  simpa [J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul, sub_eq_add_neg,
    add_comm] using h

end Multiplier

section Map

variable {S : Type*} [CommRing S]

/-- A ring homomorphism carries symplectic similitudes to symplectic similitudes. -/
theorem map_mem (f : R →+* S) {M : GL (l ⊕ l) R} (hM : M ∈ GLSymplecticSimilitude l R) :
    Matrix.GeneralLinearGroup.map f M ∈ GLSymplecticSimilitude l S := by
  obtain ⟨c, hc⟩ := hM
  refine ⟨Units.map f c, ?_⟩
  have h := congrArg (fun N : Matrix (l ⊕ l) (l ⊕ l) R => N.map f) hc
  simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.map_smul', Matrix.map_J] using h

variable (l) in
/-- The homomorphism between similitude groups induced by a ring homomorphism: the restriction of
the entrywise map `Matrix.GeneralLinearGroup.map`. -/
def map (f : R →+* S) : GLSymplecticSimilitude l R →* GLSymplecticSimilitude l S where
  toFun M := ⟨Matrix.GeneralLinearGroup.map f M, map_mem f M.property⟩
  map_one' := Subtype.ext (map_one (Matrix.GeneralLinearGroup.map f))
  map_mul' M N := Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map f) M.val N.val)

/-- The underlying invertible matrix of `map f γ` is the entrywise image of `γ`. -/
@[simp]
theorem coe_map (f : R →+* S) (M : GLSymplecticSimilitude l R) :
    ((map l f M : GLSymplecticSimilitude l S) : GL (l ⊕ l) S) =
      Matrix.GeneralLinearGroup.map f (M : GL (l ⊕ l) R) :=
  (rfl)

/-- The map induced by the identity ring homomorphism is the identity. -/
@[simp]
theorem map_id : map l (RingHom.id R) = MonoidHom.id (GLSymplecticSimilitude l R) := by
  ext M i j
  simp

/-- The map induced by a composite of ring homomorphisms is the composite of the induced maps. -/
theorem map_comp {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) :
    map l (g.comp f) = (map l g).comp (map l f) := by
  ext M i j
  simp

/-- **The multiplier commutes with change of rings.** -/
@[simp]
theorem multiplier_map [Nonempty l] (f : R →+* S) (M : GLSymplecticSimilitude l R) :
    multiplier l S (map l f M) = Units.map f (multiplier l R M) := by
  rw [multiplier_eq_iff]
  have h := congrArg (fun N : Matrix (l ⊕ l) (l ⊕ l) R => N.map f) (mul_J_mul_transpose M)
  simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.map_smul', Matrix.map_J] using h

end Map

section GenusOne

variable [Unique l]

/-- **In genus one every invertible matrix is a symplectic similitude**: `GSp₂ = GL₂`. -/
theorem eq_top_of_unique : GLSymplecticSimilitude l R = ⊤ := by
  refine eq_top_iff.2 fun M _ => ⟨Matrix.GeneralLinearGroup.det M, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.mul_J_mul_transpose_eq_det_smul _

/-- **In genus one the multiplier is the determinant.** -/
theorem multiplier_eq_det (M : GLSymplecticSimilitude l R) :
    multiplier l R M = Matrix.GeneralLinearGroup.det (M : GL (l ⊕ l) R) := by
  rw [multiplier_eq_iff, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.mul_J_mul_transpose_eq_det_smul _

end GenusOne

end GLSymplecticSimilitude

end TauCeti
