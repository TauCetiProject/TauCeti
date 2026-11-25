/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.HeckeRing.Associativity
public import TauCeti.NumberTheory.HeckeRing.Map.Submonoid
public import TauCeti.NumberTheory.HeckeRing.Normalizer
public import TauCeti.NumberTheory.Padics.GeneralLinearGroup.Integral

import Mathlib.Tactic.Group
import TauCeti.GroupTheory.Commensurable
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.Padics.Matrix

/-!
# The local `p`-adic Hecke rings of `GL_n`

Inside `GL_n(ℚ_p)` consider the compact open subgroup `K = GL_n(ℤ_p)` (`TauCeti.GLPadicInt`) and
the submonoid `Δ_p = M_n(ℤ_p) ∩ GL_n(ℚ_p)` of invertible matrices with entries in `ℤ_p`. This file
shows that `(K, Δ_p)` and `(K, GL_n(ℚ_p))` are Hecke pairs, which founds the *integral* local
Hecke ring `H(GL_n(ℤ_p), Δ_p)` and the *rational* local Hecke ring `H(GL_n(ℤ_p), GL_n(ℚ_p))`, and
embeds the first into the second by enlarging the submonoid.

These are the local counterparts of the global rings `HeckeRing.GLn.IntegralHeckeRing` and
`HeckeRing.GLn.FullHeckeRing`. Rhodes and Shemanske compare the `p`-primary part of the integral
Hecke ring of `GL_n` over `ℤ` with the integral local ring, by sending a `p`-primary lattice to its
`ℤ_p`-completion; that comparison is not made here. The central scalar `p I` lies in `Δ_p` while
`p⁻¹ I` does not, and its double coset becomes a unit of the rational local ring
(`HeckeRing.GLn.padicScalarUnit`).

The heart is that **every element of `GL_n(ℚ_p)` commensurates `GL_n(ℤ_p)`**
(`HeckeRing.GLn.commensurator_glPadicInt_eq_top`). For `g ∈ GL_n(ℚ_p)` choose `k, l` with
`A = p ^ k g` and `B = p ^ l g⁻¹` integral (`Matrix.exists_map_padicInt_eq_pow_smul`). If
`γ ∈ GL_n(ℤ_p)` is congruent to `1` modulo `p ^ (k + l)`, say `γ = 1 + p ^ (k + l) C`
(`PadicInt.exists_eq_one_add_pow_smul_of_mem_ker`), then
`g⁻¹ γ g = 1 + B C A` is integral, and so is its inverse `g⁻¹ γ⁻¹ g`, so `g⁻¹ γ g ∈ GL_n(ℤ_p)`.
Thus the principal congruence subgroup of level `p ^ (k + l)`, the kernel of reduction
`GL_n(ℤ_p) → GL_n(ℤ/p^(k+l)ℤ)` and so of finite index in `GL_n(ℤ_p)`, lies in `g GL_n(ℤ_p) g⁻¹`.
By `Subgroup.Commensurable.commensurator_eq_top_iff` this one inclusion for every `g` suffices.

## Main definitions

* `HeckeRing.GLn.padicIntEntries ι p`: the submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of `GL_n(ℚ_p)`,
  for any finite index type `ι`.
* `HeckeRing.GLn.PadicIntegralHeckeRing n p`, `HeckeRing.GLn.PadicRationalHeckeRing n p`: the
  Hecke rings of `(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))` and `(GL_n(ℤ_p), GL_n(ℚ_p))` over `ℤ`.
* `HeckeRing.GLn.padicIntegralToRationalRingHom`: the injective ring homomorphism between them,
  over any coefficient semiring.

## Main results

* `HeckeRing.GLn.mem_padicIntEntries_iff`, `HeckeRing.GLn.mem_padicIntEntries_iff_norm_le_one`:
  membership in `Δ_p` is integrality of the entries.
* `HeckeRing.GLn.mem_glPadicInt_iff_mem_padicIntEntries_and_inv_mem`: `g ∈ GL_n(ℤ_p)` exactly
  when `g` and `g⁻¹` lie in `Δ_p`.
* `HeckeRing.GLn.commensurator_glPadicInt_eq_top`: the commensurator of `GL_n(ℤ_p)` in `GL_n(ℚ_p)`
  is the whole group.
* the `IsHeckeTriple` instances for `(Δ_p, GL_n(ℤ_p))` and `(GL_n(ℚ_p), GL_n(ℤ_p))`.
* `HeckeRing.GLn.padicScalar_mem_padicIntEntries`,
  `HeckeRing.GLn.padicScalar_inv_notMem_padicIntEntries`: `p I ∈ Δ_p`, and `p⁻¹ I ∉ Δ_p` in
  positive rank.
* `HeckeRing.GLn.padicScalarUnit`, `HeckeRing.GLn.val_padicScalarUnit`,
  `HeckeRing.GLn.val_inv_padicScalarUnit`: the central coset `[K (p I) K]` of the integral local
  ring is a unit of the rational one, with inverse `[K (p⁻¹ I) K]`.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.1.
* [J. A. Rhodes and T. R. Shemanske,
  *Rationality theorems for Hecke operators on GL_n*][rhodes1999], §3.
-/

public section

open Matrix Subgroup Subgroup.Commensurable TauCeti
open scoped Pointwise HeckeCosetModule

namespace HeckeRing.GLn

variable (ι : Type*) [Fintype ι] [DecidableEq ι] (n p : ℕ) [Fact p.Prime]

section Subgroups

/-- The submonoid `M_n(ℤ_p) ∩ GL_n(ℚ_p)` of `GL_n(ℚ_p)`: invertible matrices over `ℚ_p` whose
entries are `p`-adic integers. Membership is characterized by `mem_padicIntEntries_iff` and
`mem_padicIntEntries_iff_norm_le_one`. -/
noncomputable def padicIntEntries : Submonoid (GL ι ℚ_[p]) :=
  ((PadicInt.Coe.ringHom (p := p)).mapMatrix (m := ι)).range.toSubmonoid.comap
    (Units.coeHom _)

variable {ι p}

/-- The image of a matrix in `GL_n(ℤ_p)` is the entrywise image of the underlying matrix. -/
private lemma coe_map_coe (u : GL ι ℤ_[p]) :
    (GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) u : Matrix ι ι ℚ_[p]) =
      (u : Matrix ι ι ℤ_[p]).map ((↑) : ℤ_[p] → ℚ_[p]) :=
  (rfl)

/-- The entrywise image of a matrix over `ℤ_p` is its image under the ring homomorphism
`M_n(ℤ_p) → M_n(ℚ_p)`, through which it is multiplicative. -/
private lemma map_coe_eq_mapMatrix (A : Matrix ι ι ℤ_[p]) :
    A.map ((↑) : ℤ_[p] → ℚ_[p]) = (PadicInt.Coe.ringHom (p := p)).mapMatrix A :=
  (rfl)

/-- Membership in `M_n(ℤ_p) ∩ GL_n(ℚ_p)`: `g` is the entrywise image of a matrix over `ℤ_p`. -/
theorem mem_padicIntEntries_iff {g : GL ι ℚ_[p]} :
    g ∈ padicIntEntries ι p ↔
      ∃ A : Matrix ι ι ℤ_[p], A.map ((↑) : ℤ_[p] → ℚ_[p]) = g := by
  simp_rw [padicIntEntries, Submonoid.mem_comap, Subring.mem_toSubmonoid, RingHom.mem_range,
    map_coe_eq_mapMatrix, Units.coeHom_apply]

/-- Membership in `M_n(ℤ_p) ∩ GL_n(ℚ_p)`: every entry has `p`-adic norm at most `1`. -/
theorem mem_padicIntEntries_iff_norm_le_one {g : GL ι ℚ_[p]} :
    g ∈ padicIntEntries ι p ↔ ∀ i j, ‖(g : Matrix ι ι ℚ_[p]) i j‖ ≤ 1 := by
  rw [mem_padicIntEntries_iff]
  refine ⟨?_, fun h ↦ ⟨Matrix.of fun i j ↦ ⟨_, h i j⟩, by ext; rfl⟩⟩
  rintro ⟨A, hA⟩ i j
  rw [← hA]
  exact (A i j).property

/-- **`GL_n(ℤ_p)` inside `GL_n(ℚ_p)`**: an invertible `p`-adic matrix lies in `GL_n(ℤ_p)`
exactly when both it and its inverse have entries in `ℤ_p`. -/
theorem mem_glPadicInt_iff_mem_padicIntEntries_and_inv_mem {g : GL ι ℚ_[p]} :
    g ∈ GLPadicInt ι p ↔ g ∈ padicIntEntries ι p ∧ g⁻¹ ∈ padicIntEntries ι p := by
  simp_rw [mem_padicIntEntries_iff_norm_le_one]
  exact GLPadicInt.mem_iff_inv

/-- `GL_n(ℤ_p) ≤ M_n(ℤ_p) ∩ GL_n(ℚ_p)`. -/
theorem glPadicInt_le_padicIntEntries :
    (GLPadicInt ι p).toSubmonoid ≤ padicIntEntries ι p :=
  fun _ hg ↦ (mem_glPadicInt_iff_mem_padicIntEntries_and_inv_mem.mp hg).1

end Subgroups

section Commensurator

variable {ι p}

/-- **The conjugation step.** If `p ^ k g` and `p ^ l g⁻¹` are integral and `γ ∈ GL_n(ℤ_p)` is
congruent to `1` modulo `p ^ (k + l)`, then `g⁻¹ γ g` is integral. -/
private lemma inv_mul_map_mul_mem_padicIntEntries {g : GL ι ℚ_[p]} {k l : ℕ}
    {A B : Matrix ι ι ℤ_[p]}
    (hA : A.map ((↑) : ℤ_[p] → ℚ_[p]) = (p : ℚ_[p]) ^ k • (g : Matrix ι ι ℚ_[p]))
    (hB : B.map ((↑) : ℤ_[p] → ℚ_[p]) = (p : ℚ_[p]) ^ l • (↑g⁻¹ : Matrix ι ι ℚ_[p]))
    {γ : GL ι ℤ_[p]}
    (hγ : γ ∈ (GeneralLinearGroup.map (PadicInt.toZModPow (p := p) (k + l))).ker) :
    g⁻¹ * GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) γ * g ∈
      padicIntEntries ι p := by
  obtain ⟨C, hC⟩ := PadicInt.exists_eq_one_add_pow_smul_of_mem_ker hγ
  set f := (PadicInt.Coe.ringHom (p := p)).mapMatrix (m := ι)
  rw [map_coe_eq_mapMatrix] at hA hB
  have hfγ : f γ = 1 + ((p : ℚ_[p]) ^ (k + l)) • f C := by
    rw [hC, map_add, map_one]
    ext i j
    simp [f]
  -- the key identity `(p ^ l g⁻¹) C (p ^ k g) = p ^ (k + l) g⁻¹ C g`
  have hBCA : f (B * C * A) = (p : ℚ_[p]) ^ (k + l) •
      ((↑g⁻¹ : Matrix ι ι ℚ_[p]) * f C * (g : Matrix ι ι ℚ_[p])) := by
    rw [map_mul, map_mul, hA, hB, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      ← pow_add, add_comm l k]
  -- so `g⁻¹ (1 + p ^ (k + l) C) g = 1 + B C A` is integral
  refine mem_padicIntEntries_iff.mpr ⟨1 + B * C * A, ?_⟩
  rw [map_coe_eq_mapMatrix, map_add, map_one, hBCA, Units.val_mul, Units.val_mul, coe_map_coe,
    map_coe_eq_mapMatrix, hfγ]
  simp [mul_add, add_mul]

/-- **Every element of `GL_n(ℚ_p)` commensurates `GL_n(ℤ_p)`.** For `g ∈ GL_n(ℚ_p)`, a principal
congruence subgroup of `GL_n(ℤ_p)`, of finite index, lies in `g GL_n(ℤ_p) g⁻¹`. -/
theorem commensurator_glPadicInt_eq_top : commensurator (GLPadicInt ι p) = ⊤ := by
  refine commensurator_eq_top_iff.mpr fun g ↦ ?_
  obtain ⟨k, A, hA⟩ := exists_map_padicInt_eq_pow_smul (p := p) (g : Matrix ι ι ℚ_[p])
  obtain ⟨l, B, hB⟩ := exists_map_padicInt_eq_pow_smul (p := p) (↑g⁻¹ : Matrix ι ι ℚ_[p])
  set φ := GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := p)) (n := ι)
  set K := (GeneralLinearGroup.map (PadicInt.toZModPow (p := p) (k + l)) (n := ι)).ker
  have hφ : Function.Injective φ := GeneralLinearGroup.map_injective fun _ _ ↦ PadicInt.ext
  have hrange : GLPadicInt ι p = φ.range := by
    ext
    exact GLPadicInt.mem_iff_exists_map.trans MonoidHom.mem_range.symm
  -- the principal congruence subgroup has finite index in `GL_n(ℤ_p)`
  have hK : (K.map φ).IsFiniteRelIndex (GLPadicInt ι p) := by
    rw [isFiniteRelIndex_iff_relIndex_ne_zero, hrange, MonoidHom.range_eq_map,
      relIndex_map_map_of_injective _ _ hφ, relIndex_top_right]
    exact (finiteIndex_ker _).index_ne_zero
  refine isFiniteRelIndex_of_le_left (GLPadicInt ι p) (H := K.map φ) ?_
  -- and it lies in `g GL_n(ℤ_p) g⁻¹`
  rintro _ ⟨γ, hγ, rfl⟩
  rw [mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
    mem_glPadicInt_iff_mem_padicIntEntries_and_inv_mem]
  refine ⟨inv_mul_map_mul_mem_padicIntEntries hA hB hγ, ?_⟩
  have hinv : (g⁻¹ * φ γ * g)⁻¹ = g⁻¹ * φ γ⁻¹ * g := by rw [map_inv]; group
  rw [hinv]
  exact inv_mul_map_mul_mem_padicIntEntries hA hB (K.inv_mem hγ)

/-- The integral local Hecke pair `(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))`. -/
instance instIsHeckeTriplePadicIntEntriesGLPadicInt :
    IsHeckeTriple (padicIntEntries ι p) (GLPadicInt ι p) (GLPadicInt ι p) :=
  IsHeckeTriple.of_diagonal glPadicInt_le_padicIntEntries
    (by rw [commensurator_glPadicInt_eq_top]; exact le_top)

/-- The rational local Hecke pair `(GL_n(ℤ_p), GL_n(ℚ_p))`. -/
instance instIsHeckeTripleTopGLPadicInt :
    IsHeckeTriple (⊤ : Submonoid (GL ι ℚ_[p])) (GLPadicInt ι p) (GLPadicInt ι p) :=
  IsHeckeTriple.of_diagonal le_top (by rw [commensurator_glPadicInt_eq_top]; exact le_top)

end Commensurator

section Rings

/-- The integral local Hecke ring `H(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))` over `ℤ`. -/
abbrev PadicIntegralHeckeRing := 𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) ℤ

/-- The rational local Hecke ring `H(GL_n(ℤ_p), GL_n(ℚ_p))` over `ℤ`. -/
abbrev PadicRationalHeckeRing := 𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) ℤ

/-- **The integral local Hecke ring inside the rational one**: enlarging
`M_n(ℤ_p) ∩ GL_n(ℚ_p)` to `GL_n(ℚ_p)` embeds `H(GL_n(ℤ_p), M_n(ℤ_p) ∩ GL_n(ℚ_p))` into
`H(GL_n(ℤ_p), GL_n(ℚ_p))`, over any coefficient semiring `R`. -/
noncomputable def padicIntegralToRationalRingHom (R : Type*) [Semiring R] :
    𝕋 (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) R →+*
      𝕋 (⊤ : Submonoid (GL (Fin n) ℚ_[p])) (GLPadicInt (Fin n) p) R :=
  HeckeCosetModule.mapSubmonoidRingHom R le_top

/-- `padicIntegralToRationalRingHom` sends a basis element to the basis element of the same
double coset. -/
@[simp]
theorem padicIntegralToRationalRingHom_single (R : Type*) [Semiring R]
    (D : HeckeCoset (padicIntEntries (Fin n) p) (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p))
    (b : R) :
    padicIntegralToRationalRingHom n p R (HeckeCosetModule.single R D b) =
      HeckeCosetModule.single R (D.map le_top le_rfl le_rfl) b :=
  HeckeCosetModule.mapSubmonoidRingHom_single R le_top D b

/-- `padicIntegralToRationalRingHom` is injective. -/
theorem padicIntegralToRationalRingHom_injective (R : Type*) [Semiring R] :
    Function.Injective (padicIntegralToRationalRingHom n p R) :=
  HeckeCosetModule.mapSubmonoidRingHom_injective R le_top

end Rings

section Scalar

/-- The central scalar matrix `p I` in `GL_n(ℚ_p)`. -/
noncomputable def padicScalar : GL (Fin n) ℚ_[p] :=
  GeneralLinearGroup.scalar (Fin n)
    (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

/-- The underlying matrix of `padicScalar` is the scalar matrix `p I`. -/
@[simp]
theorem coe_padicScalar :
    (padicScalar n p : Matrix (Fin n) (Fin n) ℚ_[p]) = Matrix.scalar (Fin n) (p : ℚ_[p]) :=
  (rfl)

/-- The underlying matrix of the inverse of `padicScalar` is the scalar matrix `p⁻¹ I`. -/
-- Not a simp lemma: `Matrix.coe_units_inv` and `coe_padicScalar` already rewrite the left-hand
-- side to the matrix inverse of `p I`, so the simpNF linter rejects it.
theorem coe_inv_padicScalar :
    (↑(padicScalar n p)⁻¹ : Matrix (Fin n) (Fin n) ℚ_[p]) =
      Matrix.scalar (Fin n) (p : ℚ_[p])⁻¹ := by
  rw [padicScalar, ← map_inv, GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
    Units.val_mk0]

/-- `p I` is central in `GL_n(ℚ_p)`. -/
theorem padicScalar_mem_center : padicScalar n p ∈ center (GL (Fin n) ℚ_[p]) := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨_, rfl⟩

/-- `p I` has entries in `ℤ_p`. -/
theorem padicScalar_mem_padicIntEntries : padicScalar n p ∈ padicIntEntries (Fin n) p := by
  refine mem_padicIntEntries_iff_norm_le_one.mpr fun i j ↦ ?_
  rw [coe_padicScalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [Padic.norm_p]
    exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Fact.out : p.Prime).one_le)
  · simp

/-- In positive rank, `p⁻¹ I` does not have entries in `ℤ_p`: the coset `[K (p⁻¹ I) K]`, the
inverse of `[K (p I) K]` in the rational local Hecke ring, is not a double coset of the integral
local Hecke pair. -/
theorem padicScalar_inv_notMem_padicIntEntries [NeZero n] :
    (padicScalar n p)⁻¹ ∉ padicIntEntries (Fin n) p := by
  rw [mem_padicIntEntries_iff_norm_le_one]
  intro h
  have h00 := h 0 0
  rw [coe_inv_padicScalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq, norm_inv, Padic.norm_p,
    inv_inv] at h00
  exact (Fact.out : p.Prime).one_lt.not_ge (mod_cast h00)

/-- **The central coset `[K (p I) K]` is a unit of the rational local Hecke ring**, with inverse
`[K (p⁻¹ I) K]`, since `p I` is central. -/
noncomputable def padicScalarUnit : (PadicRationalHeckeRing n p)ˣ :=
  HeckeCosetModule.unitOfMemNormalizer ℤ (Submonoid.mem_top _) (Submonoid.mem_top _)
    (center_le_normalizer _ (padicScalar_mem_center n p))

/-- The underlying element of `padicScalarUnit` is the image of the central coset `[K (p I) K]`
of the integral local Hecke ring. -/
@[simp]
theorem val_padicScalarUnit :
    (padicScalarUnit n p : PadicRationalHeckeRing n p) =
      padicIntegralToRationalRingHom n p ℤ (HeckeCosetModule.single ℤ
        (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)
          ⟨padicScalar n p, padicScalar_mem_padicIntEntries n p⟩) 1) := by
  simp only [padicScalarUnit, HeckeCosetModule.val_unitOfMemNormalizer,
    padicIntegralToRationalRingHom_single, HeckeCoset.map_mk]
  exact congrArg (HeckeCosetModule.single ℤ · 1)
    (HeckeCoset.mk_congr_val (Submonoid.coe_inclusion le_top _).symm)

/-- The inverse of `padicScalarUnit` is the central coset `[K (p⁻¹ I) K]`. -/
@[simp]
theorem val_inv_padicScalarUnit :
    (↑(padicScalarUnit n p)⁻¹ : PadicRationalHeckeRing n p) =
      HeckeCosetModule.single ℤ (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)
        ⟨(padicScalar n p)⁻¹, Submonoid.mem_top _⟩) 1 :=
  HeckeCosetModule.val_inv_unitOfMemNormalizer _ _ _ _

/-- The central coset `[K (p I) K]` of the integral local Hecke ring becomes a unit in the rational
one. -/
theorem isUnit_padicIntegralToRationalRingHom_single_padicScalar :
    IsUnit (padicIntegralToRationalRingHom n p ℤ (HeckeCosetModule.single ℤ
      (HeckeCoset.mk (GLPadicInt (Fin n) p) (GLPadicInt (Fin n) p)
        ⟨padicScalar n p, padicScalar_mem_padicIntEntries n p⟩) 1)) :=
  val_padicScalarUnit n p ▸ (padicScalarUnit n p).isUnit

end Scalar

end HeckeRing.GLn
