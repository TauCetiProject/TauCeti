/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic

/-!
# The symplectic similitude group `GSp`

For a commutative ring `R` and a finite index type `l`, the **symplectic similitude group**
(general symplectic group) `GSp(l ⊕ l, R)` is the subgroup of `GL (l ⊕ l) R` of the invertible
matrices `γ` that scale the standard alternating form `J = Matrix.J l R` by a unit:

```text
γ J γᵀ = c • J      for some c ∈ Rˣ.
```

When `l` is nonempty the unit `c` is determined by `γ`; it is the **similitude multiplier**
`TauCeti.GSp.multiplier γ`, and `TauCeti.GSp.multiplier : GSp l R →* Rˣ` is a group morphism whose
kernel is the symplectic group `TauCeti.GLSymplectic l R`. The Siegel cocharacter
`μ(c) = diag(1, c)` (`TauCeti.GSp.siegelCocharacter`) is a section of the multiplier, so the
multiplier is surjective and every similitude is a symplectic matrix times `μ(c)`. Together with
Mathlib's `Matrix.SymplecticGroup.det_eq_one` this computes the determinant: `det γ = c(γ) ^ g`,
where `g` is the cardinality of `l` (`TauCeti.GSp.det_eq_multiplier_pow`). For `g > 1` the
determinant therefore need not determine the multiplier: for even `g`, the multipliers `1` and
`-1` give the same determinant.

In genus one (`l` a singleton) every invertible matrix is a similitude, with multiplier its
determinant: `γ J γᵀ = det(γ) • J` (`TauCeti.GSp.mul_J_mul_transpose_eq_det_smul`), so
`GSp(2) = GL₂`.

The multiplier condition can be written as `γ J γᵀ = c • J` or as `γᵀ J γ = c • J`
(`TauCeti.GSp.mem_iff'`); the inverse of a similitude is `-c⁻¹ • J γᵀ J`
(`TauCeti.GSp.coe_inv`). A ring morphism `f : R →+* S` induces `TauCeti.GSp.map l f`, the
restriction of `Matrix.GeneralLinearGroup.map`, and the multiplier commutes with it; this is the
reduction map used to define congruence level subgroups.

## Main definitions

* `TauCeti.GSp l R`: the symplectic similitude group, as a subgroup of `GL (l ⊕ l) R`.
* `TauCeti.GSp.multiplier`: the similitude multiplier `GSp l R →* Rˣ`, for nonempty `l`.
* `TauCeti.GSp.siegelCocharacter`: the cocharacter `c ↦ diag(1, c)`, a section of the multiplier.
* `TauCeti.GSp.map`: the morphism induced by a ring morphism of value rings.

## Main results

* `TauCeti.GSp.mul_J_mul_transpose` and `TauCeti.GSp.transpose_mul_J_mul`: the defining
  identities `γ J γᵀ = c(γ) • J` and `γᵀ J γ = c(γ) • J`.
* `TauCeti.GSp.ker_multiplier`: the kernel of the multiplier is the symplectic group.
* `TauCeti.GSp.multiplier_surjective`: the multiplier is surjective.
* `TauCeti.GSp.det_eq_multiplier_pow`: `det γ = c(γ) ^ g`.
* `TauCeti.GSp.eq_top_of_unique` and `TauCeti.GSp.multiplier_eq_det`: in genus one every
  invertible matrix is a similitude and the multiplier is the determinant.

## References

* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. 182
  (2015), §3.1: the group `GSp_2g` and its similitude factor.
* J. S. Milne, *Introduction to Shimura varieties* (2005), §6: the group `GSp(V, ψ)` of
  symplectic similitudes and its multiplier `ν`.
-/

public section

open Matrix

namespace TauCeti

universe u

variable (l : Type*) [DecidableEq l] [Fintype l] (R : Type u) [CommRing R]

/-- Similitudes compose: if `M` scales `J` by `a` and `N` scales `J` by `b`, then `M * N` scales
`J` by `a * b`. -/
private theorem mul_J_mul_transpose_mul {M N : Matrix (l ⊕ l) (l ⊕ l) R} {a b : R}
    (hM : M * J l R * Mᵀ = a • J l R) (hN : N * J l R * Nᵀ = b • J l R) :
    M * N * J l R * (M * N)ᵀ = (a * b) • J l R := by
  calc M * N * J l R * (M * N)ᵀ = M * (N * J l R * Nᵀ) * Mᵀ := by
        simp only [transpose_mul, Matrix.mul_assoc]
    _ = (a * b) • J l R := by
        rw [hN, Matrix.mul_smul, Matrix.smul_mul, hM, smul_smul, mul_comm]

/-- If `N` is a left inverse of `M` and `M` scales `J` by `c`, then so does `Mᵀ`. -/
private theorem transpose_mul_J_mul_of_mul_J_mul_transpose {M N : Matrix (l ⊕ l) (l ⊕ l) R}
    (hNM : N * M = 1) {c : R} (h : M * J l R * Mᵀ = c • J l R) :
    Mᵀ * J l R * M = c • J l R := by
  have h₁ : J l R * Mᵀ = c • (N * J l R) := by
    calc J l R * Mᵀ = N * (M * J l R * Mᵀ) := by
          simp only [← Matrix.mul_assoc, hNM, Matrix.one_mul]
      _ = c • (N * J l R) := by rw [h, Matrix.mul_smul]
  calc Mᵀ * J l R * M = -(J l R * J l R) * Mᵀ * J l R * M := by
        rw [J_squared, neg_neg, Matrix.one_mul]
    _ = -(J l R * (J l R * Mᵀ) * J l R * M) := by
        simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = c • (J l R * N * (-(J l R * J l R)) * M) := by
        rw [h₁]
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg,
          Matrix.mul_assoc]
    _ = c • J l R := by
        rw [J_squared, neg_neg, Matrix.mul_one, Matrix.mul_assoc, hNM, Matrix.mul_one]

/-- The **symplectic similitude group** `GSp(l ⊕ l, R)`: the invertible matrices `γ` with
`γ J γᵀ = c • J` for some unit `c`, where `J = Matrix.J l R` is the standard alternating form. -/
def GSp : Subgroup (GL (l ⊕ l) R) where
  carrier := {M | ∃ c : Rˣ,
    (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (c : R) • J l R}
  mul_mem' := by
    rintro M N ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by
      simpa only [Units.val_mul] using mul_J_mul_transpose_mul l R ha hb⟩
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro M ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    set N : Matrix (l ⊕ l) (l ⊕ l) R := ((M⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)
    have hNM : N * (M : Matrix (l ⊕ l) (l ⊕ l) R) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc N * J l R * Nᵀ = ((c⁻¹ : Rˣ) : R) • (N * ((c : R) • J l R) * Nᵀ) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Units.inv_mul, one_smul]
      _ = ((c⁻¹ : Rˣ) : R) •
            ((N * (M : Matrix (l ⊕ l) (l ⊕ l) R)) * J l R *
              (N * (M : Matrix (l ⊕ l) (l ⊕ l) R))ᵀ) := by
          rw [← hc]
          simp only [transpose_mul, Matrix.mul_assoc]
      _ = ((c⁻¹ : Rˣ) : R) • J l R := by
          rw [hNM, Matrix.one_mul, transpose_one, Matrix.mul_one]

namespace GSp

variable {l R}

/-- Membership in the similitude group, in the form `γ J γᵀ = c • J`. -/
theorem mem_iff {M : GL (l ⊕ l) R} :
    M ∈ GSp l R ↔ ∃ c : Rˣ,
      (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ =
        (c : R) • J l R :=
  Iff.rfl

/-- For an invertible matrix, `γ J γᵀ = c • J` and `γᵀ J γ = c • J` are equivalent, for every
scalar `c`. -/
theorem mul_J_mul_transpose_eq_smul_iff (M : GL (l ⊕ l) R) (c : R) :
    (M : Matrix (l ⊕ l) (l ⊕ l) R) * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = c • J l R ↔
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R) = c • J l R := by
  have hNM : ((M⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) *
      (M : Matrix (l ⊕ l) (l ⊕ l) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMN : (M : Matrix (l ⊕ l) (l ⊕ l) R) *
      ((M⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨transpose_mul_J_mul_of_mul_J_mul_transpose l R hNM, fun h ↦ ?_⟩
  have hT : ((M⁻¹ : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ *
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = 1 := by
    rw [← transpose_mul, hMN, transpose_one]
  simpa only [transpose_transpose] using
    transpose_mul_J_mul_of_mul_J_mul_transpose l R hT (by simpa only [transpose_transpose] using h)

/-- Membership in the similitude group, in the transposed form `γᵀ J γ = c • J`. -/
theorem mem_iff' {M : GL (l ⊕ l) R} :
    M ∈ GSp l R ↔ ∃ c : Rˣ,
      (M : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R * (M : Matrix (l ⊕ l) (l ⊕ l) R) =
        (c : R) • J l R := by
  simp only [mem_iff, mul_J_mul_transpose_eq_smul_iff]

/-- The similitude group is closed under transposition, written `star` on the units of a matrix
ring over a ring with trivial star. -/
theorem star_mem [StarRing R] [TrivialStar R] {M : GL (l ⊕ l) R} (hM : M ∈ GSp l R) :
    star M ∈ GSp l R := by
  obtain ⟨c, hc⟩ := mem_iff'.1 hM
  refine ⟨c, ?_⟩
  rw [Units.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
    transpose_transpose, hc]

variable (l R) in
/-- Every symplectic matrix is a similitude, with multiplier `1`. -/
theorem GLSymplectic_le_GSp : GLSymplectic l R ≤ GSp l R :=
  fun _ hM ↦ ⟨1, by rw [Units.val_one, one_smul]; exact GLSymplectic.mem_iff.1 hM⟩

section Multiplier

variable [Nonempty l]

omit [Fintype l] in
variable (l R) in
/-- For nonempty `l`, the scalar multiples of `J` determine the scalar. -/
theorem smul_J_injective : Function.Injective fun c : R ↦ c • J l R := by
  intro c d h
  obtain ⟨i⟩ := ‹Nonempty l›
  simpa [Matrix.J] using congrFun (congrFun h (Sum.inr i)) (Sum.inl i)

/-- The similitude factor is unique: two scalars by which an invertible matrix scales `J` agree. -/
theorem eq_of_mul_J_mul_transpose_eq {M : Matrix (l ⊕ l) (l ⊕ l) R} {c d : R}
    (hc : M * J l R * Mᵀ = c • J l R) (hd : M * J l R * Mᵀ = d • J l R) : c = d :=
  smul_J_injective l R (hc.symm.trans hd)

variable (l R) in
/-- The **similitude multiplier** `c : GSp l R →* Rˣ`, characterized by `γ J γᵀ = c(γ) • J`
(`TauCeti.GSp.mul_J_mul_transpose`). Its kernel is the symplectic group
(`TauCeti.GSp.ker_multiplier`). -/
noncomputable def multiplier : GSp l R →* Rˣ where
  toFun M := (mem_iff.1 M.property).choose
  map_one' := Units.ext <|
    eq_of_mul_J_mul_transpose_eq (mem_iff.1 (1 : GSp l R).property).choose_spec (by simp)
  map_mul' M N := Units.ext <|
    eq_of_mul_J_mul_transpose_eq (mem_iff.1 (M * N).property).choose_spec <| by
      simpa only [Subgroup.coe_mul, Units.val_mul] using
        mul_J_mul_transpose_mul l R (mem_iff.1 M.property).choose_spec
          (mem_iff.1 N.property).choose_spec

/-- **The defining identity of the multiplier**: `γ J γᵀ = c(γ) • J`. -/
theorem mul_J_mul_transpose (M : GSp l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ =
      (multiplier l R M : R) • J l R :=
  (mem_iff.1 M.property).choose_spec

/-- The transposed defining identity of the multiplier: `γᵀ J γ = c(γ) • J`. -/
theorem transpose_mul_J_mul (M : GSp l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R *
        ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      (multiplier l R M : R) • J l R :=
  (mul_J_mul_transpose_eq_smul_iff _ _).1 (mul_J_mul_transpose M)

/-- The multiplier is the unit by which a similitude scales `J`. -/
theorem multiplier_eq_iff {M : GSp l R} {c : Rˣ} :
    multiplier l R M = c ↔
      ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) * J l R *
          ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ = (c : R) • J l R := by
  refine ⟨fun h ↦ h ▸ mul_J_mul_transpose M, fun h ↦ Units.ext ?_⟩
  exact eq_of_mul_J_mul_transpose_eq (mul_J_mul_transpose M) h

/-- **The inverse of a similitude**: `γ⁻¹ = -c(γ)⁻¹ • J γᵀ J`. -/
theorem coe_inv (M : GSp l R) :
    ((M⁻¹ : GSp l R) : GL (l ⊕ l) R).val =
      -(((multiplier l R M)⁻¹ : Rˣ) : R) •
        (J l R * ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R)ᵀ * J l R) := by
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_J_mul_transpose,
    Matrix.smul_mul, J_squared, smul_smul]
  simp

/-- A similitude is symplectic exactly when its multiplier is `1`. -/
theorem mem_GLSymplectic_iff (M : GSp l R) :
    (M : GL (l ⊕ l) R) ∈ GLSymplectic l R ↔ multiplier l R M = 1 := by
  rw [GLSymplectic.mem_iff, multiplier_eq_iff, Units.val_one, one_smul]

variable (l R) in
/-- **The kernel of the multiplier is the symplectic group.** -/
theorem ker_multiplier :
    (multiplier l R).ker = (GLSymplectic l R).subgroupOf (GSp l R) := by
  ext M
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_GLSymplectic_iff]

end Multiplier

/-! ### The Siegel cocharacter -/

section SiegelCocharacter

/-- The block matrix `diag(1, c)` scales `J` by `c`. -/
private theorem fromBlocks_one_smul_one_mul_J_mul_transpose (c : R) :
    fromBlocks (1 : Matrix l l R) 0 0 (c • 1) * J l R *
        (fromBlocks (1 : Matrix l l R) 0 0 (c • 1))ᵀ = c • J l R := by
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul]

variable (l R) in
/-- The **Siegel cocharacter** `μ(c) = diag(1, c)`, the block-diagonal matrix with blocks `1` and
`c • 1`, as a morphism `Rˣ →* GSp l R`. It scales `J` by `c`, so it is a section of the
multiplier (`TauCeti.GSp.multiplier_siegelCocharacter`). -/
def siegelCocharacter : Rˣ →* GSp l R where
  toFun c := ⟨⟨fromBlocks 1 0 0 ((c : R) • 1), fromBlocks 1 0 0 (((c⁻¹ : Rˣ) : R) • 1),
    by simp [fromBlocks_multiply, smul_smul], by simp [fromBlocks_multiply, smul_smul]⟩,
    c, fromBlocks_one_smul_one_mul_J_mul_transpose (c : R)⟩
  map_one' := Subtype.ext <| Units.ext <| by simp [fromBlocks_one]
  map_mul' c d := Subtype.ext <| Units.ext <| by
    simp [fromBlocks_multiply, smul_smul, mul_comm]

/-- The underlying matrix of `μ(c)` is `diag(1, c • 1)`. -/
@[simp]
theorem coe_siegelCocharacter (c : Rˣ) :
    ((siegelCocharacter l R c : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R) =
      fromBlocks 1 0 0 ((c : R) • 1) :=
  (rfl)

/-- The determinant of `μ(c)` is `c ^ g`. -/
theorem det_siegelCocharacter (c : Rˣ) :
    ((siegelCocharacter l R c : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).det =
      (c : R) ^ Fintype.card l := by
  rw [coe_siegelCocharacter, det_fromBlocks_zero₂₁, det_one, one_mul, det_smul, det_one, mul_one]

variable [Nonempty l]

/-- **The Siegel cocharacter is a section of the multiplier**: `c(μ(c)) = c`. -/
@[simp]
theorem multiplier_siegelCocharacter (c : Rˣ) :
    multiplier l R (siegelCocharacter l R c) = c :=
  multiplier_eq_iff.2 (fromBlocks_one_smul_one_mul_J_mul_transpose (c : R))

variable (l R) in
/-- The multiplier is surjective. -/
theorem multiplier_surjective : Function.Surjective (multiplier l R) :=
  fun c ↦ ⟨siegelCocharacter l R c, multiplier_siegelCocharacter c⟩

/-- Dividing a similitude by the Siegel cocharacter of its multiplier gives a symplectic matrix. -/
theorem mul_siegelCocharacter_inv_mem_GLSymplectic (M : GSp l R) :
    ((M * (siegelCocharacter l R (multiplier l R M))⁻¹ : GSp l R) : GL (l ⊕ l) R) ∈
      GLSymplectic l R := by
  rw [mem_GLSymplectic_iff, map_mul, map_inv, multiplier_siegelCocharacter, mul_inv_cancel]

/-- **The determinant of a similitude** is the `g`-th power of its multiplier, where `g` is the
cardinality of `l`. -/
theorem det_eq_multiplier_pow (M : GSp l R) :
    ((M : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).det =
      (multiplier l R M : R) ^ Fintype.card l := by
  set μ := siegelCocharacter l R (multiplier l R M)
  have hM : M = (M * μ⁻¹) * μ := by group
  have hS : (((M * μ⁻¹ : GSp l R) : GL (l ⊕ l) R) : Matrix (l ⊕ l) (l ⊕ l) R).det = 1 :=
    SymplecticGroup.det_eq_one
      (GLSymplectic.mem_iff_mem_symplecticGroup.1 (mul_siegelCocharacter_inv_mem_GLSymplectic M))
  conv_lhs => rw [hM]
  rw [Subgroup.coe_mul, Units.val_mul, det_mul, hS, one_mul, det_siegelCocharacter]

end SiegelCocharacter

/-! ### Change of value ring -/

section Map

variable {S : Type*} [CommRing S]

/-- A ring morphism of value rings carries similitudes to similitudes, with the image
multiplier. -/
theorem map_mem (f : R →+* S) {M : GL (l ⊕ l) R} (hM : M ∈ GSp l R) :
    Matrix.GeneralLinearGroup.map f M ∈ GSp l S := by
  obtain ⟨c, hc⟩ := hM
  refine ⟨Units.map f c, ?_⟩
  have := congrArg (Matrix.map · f) hc
  simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.map_smul', map_J] using this

variable (l) in
/-- The group morphism between similitude groups induced by a ring morphism of value rings: the
restriction of `Matrix.GeneralLinearGroup.map`, which acts entrywise. -/
def map (f : R →+* S) : GSp l R →* GSp l S where
  toFun M := ⟨Matrix.GeneralLinearGroup.map f M, map_mem f M.property⟩
  map_one' := Subtype.ext (map_one (Matrix.GeneralLinearGroup.map f))
  map_mul' M N := Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map f) M.val N.val)

/-- The underlying general-linear value of the induced morphism is
`Matrix.GeneralLinearGroup.map`. -/
@[simp]
theorem coe_map (f : R →+* S) (M : GSp l R) :
    ((map l f M : GSp l S) : GL (l ⊕ l) S) =
      Matrix.GeneralLinearGroup.map f (M : GL (l ⊕ l) R) :=
  (rfl)

/-- The map induced by the identity ring morphism is the identity. -/
@[simp]
theorem map_id : map l (RingHom.id R) = MonoidHom.id (GSp l R) := by
  refine MonoidHom.ext fun M ↦ Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j ↦ ?_)
  simp

/-- The map induced by a composite of ring morphisms is the composite of the induced maps. -/
@[simp]
theorem map_comp {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) :
    map l (g.comp f) = (map l g).comp (map l f) := by
  refine MonoidHom.ext fun M ↦ Subtype.ext (Matrix.GeneralLinearGroup.ext fun i j ↦ ?_)
  simp

/-- The multiplier commutes with change of value ring. -/
@[simp]
theorem multiplier_map [Nonempty l] (f : R →+* S) (M : GSp l R) :
    multiplier l S (map l f M) = Units.map f (multiplier l R M) := by
  refine multiplier_eq_iff.2 ?_
  have := congrArg (Matrix.map · f) (mul_J_mul_transpose M)
  simpa [Matrix.map_mul, Matrix.transpose_map, Matrix.map_smul', map_J] using this

/-- The Siegel cocharacter commutes with change of value ring. -/
@[simp]
theorem map_siegelCocharacter (f : R →+* S) (c : Rˣ) :
    map l f (siegelCocharacter l R c) = siegelCocharacter l S (Units.map f c) := by
  refine Subtype.ext (Units.ext ?_)
  simp [fromBlocks_map, Matrix.map_smul', Matrix.map_one]

end Map

/-! ### Genus one -/

section GenusOne

variable [Unique l]

/-- **The genus-one form identity**: for a `2 × 2` matrix, `γ J γᵀ = det(γ) • J`. -/
theorem mul_J_mul_transpose_eq_det_smul (M : Matrix (l ⊕ l) (l ⊕ l) R) :
    M * J l R * Mᵀ = M.det • J l R := by
  set e : l ⊕ l ≃ Fin 2 :=
    (Equiv.sumCongr (Equiv.ofUnique l (Fin 1)) (Equiv.ofUnique l (Fin 1))).trans finSumFinEquiv
  have hdet : M.det =
      M (Sum.inl default) (Sum.inl default) * M (Sum.inr default) (Sum.inr default) -
        M (Sum.inl default) (Sum.inr default) * M (Sum.inr default) (Sum.inl default) := by
    have h₀ : (finSumFinEquiv (m := 1) (n := 1)).symm (0 : Fin 2) = Sum.inl 0 := rfl
    have h₁ : (finSumFinEquiv (m := 1) (n := 1)).symm (1 : Fin 2) = Sum.inr 0 := rfl
    rw [← det_reindex_self e M, det_fin_two]
    simp only [e, reindex_apply, submatrix_apply, Equiv.symm_trans_apply, h₀, h₁,
      Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr]
    simp only [Unique.eq_default]
  rw [hdet]
  ext (i | i) (j | j) <;>
    simp [Matrix.J, Matrix.mul_apply, fromBlocks, Unique.eq_default i, Unique.eq_default j] <;>
    ring

variable (l R)

/-- In genus one every invertible matrix is a similitude: `GSp(2) = GL₂`. -/
theorem eq_top_of_unique : GSp l R = ⊤ :=
  eq_top_iff.2 fun M _ ↦ ⟨Matrix.GeneralLinearGroup.det M, by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact mul_J_mul_transpose_eq_det_smul _⟩

variable {l R}

/-- In genus one the multiplier is the determinant. -/
theorem multiplier_eq_det (M : GSp l R) :
    multiplier l R M = Matrix.GeneralLinearGroup.det (M : GL (l ⊕ l) R) := by
  rw [multiplier_eq_iff, Matrix.GeneralLinearGroup.val_det_apply]
  exact mul_J_mul_transpose_eq_det_smul _

end GenusOne

end GSp

end TauCeti
