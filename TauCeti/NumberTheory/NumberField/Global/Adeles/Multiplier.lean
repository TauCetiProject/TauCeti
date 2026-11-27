/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Saturating
public import TauCeti.NumberTheory.NumberField.Global.Adeles.Lattice
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import Mathlib.Topology.Instances.Matrix
import TauCeti.LinearAlgebra.Matrix.Range
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# The multiplier of `GL_n` of the finite adeles

Let `E` be a number field, `𝔸_f` its finite adeles and `Ô` the integral ones. For
`g ∈ GL_n(𝔸_f)`, a *saturating* matrix `u ∈ GL_n(𝔸_f)` is one with `u` and `g u` integral and
`u⁻¹ = l + m g` for integral `l`, `m` (`Matrix.GeneralLinearGroup.IsSaturating`). This file shows
that saturating matrices exist and that they are exactly the `u` with `u Ôⁿ = Ôⁿ ∩ g⁻¹Ôⁿ`; two of
them differ by an element of `GL_n(Ô)` (`Matrix.GeneralLinearGroup.IsSaturating.exists_eq_mul_map`).
Hence the class `Δ(g)` of `det u` modulo the integral
units `Ô^×` depends on `g` alone (`NumberField.FiniteAdeleRing.glMultiplier`), and so does
`Δ_χ(g) = χ(det u)` for every character `χ` of the finite ideles trivial on `Ô^×`: it is the image
of `Δ(g)` under the character that `χ` induces on `𝔸_f^× / Ô^×`. Moreover `[Ôⁿ : Ôⁿ ∩ g⁻¹Ôⁿ]` is
the generalised index `[det u]`.

Existence is a lattice statement. A matrix `u` is saturating for `g` exactly when the columns of
`(u⁻¹)ᵀ` span the lattice `Ôⁿ + gᵀÔⁿ`
(`Matrix.GeneralLinearGroup.isSaturating_iff_span_col_transpose_eq`). That lattice lies between
`Ôⁿ` and `N⁻¹Ôⁿ` for an integer `N` with `N g` integral, so it has finite index in `N⁻¹Ôⁿ` (an open
subgroup of a compact one), and has a basis by `NumberField.FiniteAdeleRing.exists_mul_span_col_eq`.
The index `[Ôⁿ : u Ôⁿ]` of an integral `u` is `[det u]`
(`NumberField.FiniteAdeleRing.genIndex_det_eq_relIndex`, in
`TauCeti.NumberTheory.NumberField.Global.Adeles.Lattice`).

The multiplier satisfies the following laws, which pass to every `Δ_χ`:

* `Δ(k g k') = Δ(g)` for `k`, `k' ∈ GL_n(Ô)`, and `Δ(g) = 1` if `g` is integral;
* `Δ(k d k') = ∏ᵢ δᵢ` for `d` diagonal, where `δᵢ Ô = Ô ∩ dᵢ⁻¹ Ô`;
* `Δ(g⁻¹) = det g · Δ(g)`;
* `Δ` is multiplicative on block-diagonal matrices, and on products `a b` where `a` is `1`
  along `1 - e` and `b` is `1` along `e`, for an idempotent `e` of `𝔸_f`: for instance `a`
  supported at a set `S` of finite places and `b` supported off `S`.

## Main declarations

* `NumberField.FiniteAdeleRing.exists_isSaturating`: saturating matrices exist.
* `NumberField.FiniteAdeleRing.isSaturating_iff_span_col_eq`: `u` is saturating for `g` exactly
  when `u Ôⁿ = Ôⁿ ∩ g⁻¹Ôⁿ`.
* `Matrix.GeneralLinearGroup.IsSaturating.genIndex_det_eq_relIndex_inf`:
  `[det u] = [Ôⁿ : Ôⁿ ∩ g⁻¹Ôⁿ]` for a saturating `u`.
* `NumberField.FiniteAdeleRing.glMultiplier`: the multiplier `Δ(g)`, the class of `det u` in
  `𝔸_f^× / Ô^×`, with `Matrix.GeneralLinearGroup.IsSaturating.glMultiplier_eq` (independence of
  `u`), `Matrix.GeneralLinearGroup.IsSaturating.lift_glMultiplier` (`Δ_χ(g) = χ(det u)`),
  `glMultiplier_map_mul_mul_map`, `glMultiplier_eq_one_of_mem`,
  `glMultiplier_map_mul_diagGL_mul_map`, `glMultiplier_inv`, `glMultiplier_fromBlocksGL` and
  `glMultiplier_cutGL_mul_cutGL`.

## References

* G. Shimura, *Euler Products and Eisenstein Series*, CBMS Regional Conference Series in
  Mathematics 93, American Mathematical Society, 1997: coprime fractions of matrices and the
  denominator ideal.

## Attribution

Saturating matrices and the multiplier follow `New.IsSaturating` and `New.glMultiplier` in the
file `src/Lib/Weil/Construction/FiniteMultiplier.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), where the
multiplier is computed through elementary divisors place by place. Here saturating matrices come
instead from a basis of the lattice `Ôⁿ + gᵀÔⁿ`, and the multiplier takes values in `𝔸_f^× / Ô^×`,
which covers every character trivial on `Ô^×`.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField Matrix
open Matrix.GeneralLinearGroup
open scoped NumberField.AdeleRing

namespace NumberField.FiniteAdeleRing

variable {E : Type*} [Field E] [NumberField E] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Existence of saturating matrices -/

omit [Fintype n] [DecidableEq n] in
/-- Some nonzero integer multiple of a matrix over the finite adeles has integral entries. -/
private theorem exists_natCast_mul_mem_matrix [Finite n] (g : Matrix n n 𝔸ᶠ[E]) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ i j, (N : 𝔸ᶠ[E]) * g i j ∈ integralAdeles (𝓞 E) E := by
  have := Fintype.ofFinite n
  choose N hN0 hN using fun i j ↦ exists_natCast_mul_mem_integralAdeles (g i j)
  refine ⟨∏ i, ∏ j, N i j, Finset.prod_ne_zero_iff.2 fun i _ ↦
    Finset.prod_ne_zero_iff.2 fun j _ ↦ hN0 i j, fun i j ↦ ?_⟩
  obtain ⟨c, hc⟩ : N i j ∣ ∏ i, ∏ j, N i j :=
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i ↦ ∏ j, N i j) (Finset.mem_univ i))
  rw [hc, Nat.cast_mul, mul_comm (N i j : 𝔸ᶠ[E]), mul_assoc]
  exact mul_mem (natCast_mem _ c) (hN i j)

/-- **Saturating matrices exist** over the finite adeles: every `g ∈ GL_n(𝔸_f)` has one. -/
theorem exists_isSaturating (g : GL n 𝔸ᶠ[E]) :
    ∃ u : GL n 𝔸ᶠ[E], IsSaturating (integralAdeles (𝓞 E) E) g u := by
  -- An integer `N₀ ≠ 0` with `N₀ g` integral.
  obtain ⟨N₀, hN₀, hN₀g⟩ := exists_natCast_mul_mem_matrix (g : Matrix n n 𝔸ᶠ[E])
  replace hN₀ : (N₀ : E) ≠ 0 := Nat.cast_ne_zero.2 hN₀
  -- The lattice `Ôⁿ + gᵀ Ôⁿ` lies in `N₀⁻¹ Ôⁿ`, the column span of `b = N₀⁻¹ · 1`.
  let t : 𝔸ᶠ[E]ˣ := (hN₀.isUnit.map (algebraMap E 𝔸ᶠ[E])).unit
  have ht : (t : 𝔸ᶠ[E]) = N₀ := by simp [t]
  let b : GL n 𝔸ᶠ[E] := TauCeti.diagGL fun _ ↦ t⁻¹
  have hb {x : n → 𝔸ᶠ[E]} : x ∈ Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (b : Matrix n n 𝔸ᶠ[E]).col) ↔
        ∀ i, (N₀ : 𝔸ᶠ[E]) * x i ∈ integralAdeles (𝓞 E) E := by
    rw [mem_span_col_iff_mulVec_inv_mem, ← map_inv, TauCeti.diagGL_coe]
    simp [mulVec_diagonal, ht]
  set M := Submodule.span (integralAdeles (𝓞 E) E) (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ⊔
    Submodule.span (integralAdeles (𝓞 E) E) (Set.range (g : Matrix n n 𝔸ᶠ[E])ᵀ.col)
  have hM : M ≤ Submodule.span (integralAdeles (𝓞 E) E) (Set.range (b : Matrix n n 𝔸ᶠ[E]).col) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_) <;>
      rintro _ ⟨j, rfl⟩ <;> refine hb.2 fun i ↦ ?_
    · rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [hij]
    · exact hN₀g j i
  have hM_open : IsOpen (M : Set (n → 𝔸ᶠ[E])) :=
    Submodule.isOpen_mono le_sup_left (by simpa using isOpen_span_col (1 : GL n 𝔸ᶠ[E]))
  obtain ⟨a, ha, -⟩ := exists_mul_span_col_eq b hM
    (AddSubgroup.relIndex_ne_zero_of_isOpen_of_isCompact hM_open (isCompact_span_col b))
  -- A basis `w = b a` of `Ôⁿ + gᵀ Ôⁿ` gives the saturating matrix `(wᵀ)⁻¹`.
  refine ⟨((transposeMulEquiv n (b * a)).unop)⁻¹, isSaturating_iff_span_col_transpose_eq.2 ?_⟩
  rw [inv_inv, coe_unop_transposeMulEquiv, transpose_transpose, ha]

/-- **Saturating matrices are the bases of `Ôⁿ ∩ g⁻¹Ôⁿ`.** A matrix `u ∈ GL_n(𝔸_f)` is saturating
for `g` exactly when the `Ô`-span of its columns is `Ôⁿ ∩ g⁻¹Ôⁿ`. -/
theorem isSaturating_iff_span_col_eq {g u : GL n 𝔸ᶠ[E]} :
    IsSaturating (integralAdeles (𝓞 E) E) g u ↔
      Submodule.span (integralAdeles (𝓞 E) E) (Set.range (u : Matrix n n 𝔸ᶠ[E]).col) =
        Submodule.span (integralAdeles (𝓞 E) E) (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ⊓
          Submodule.span (integralAdeles (𝓞 E) E)
            (Set.range ((g⁻¹ : GL n 𝔸ᶠ[E]) : Matrix n n 𝔸ᶠ[E]).col) := by
  refine ⟨IsSaturating.span_col_eq, fun h ↦ ?_⟩
  obtain ⟨u₀, hu₀⟩ := exists_isSaturating g
  obtain ⟨k, rfl⟩ := exists_eq_mul_map_of_span_col_eq (hu₀.span_col_eq.trans h.symm)
  exact hu₀.mul_map k

/-- **The index of `Ôⁿ ∩ g⁻¹Ôⁿ`.** For a saturating matrix `u` of `g`,
`[Ôⁿ : Ôⁿ ∩ g⁻¹Ôⁿ]` is the generalised index of `det u`. -/
theorem _root_.Matrix.GeneralLinearGroup.IsSaturating.genIndex_det_eq_relIndex_inf
    {g u : GL n 𝔸ᶠ[E]} (h : IsSaturating (integralAdeles (𝓞 E) E) g u) :
    genIndex E (det u : 𝔸ᶠ[E]) = (Submodule.span (integralAdeles (𝓞 E) E)
      (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col) ⊓ Submodule.span (integralAdeles (𝓞 E) E)
        (Set.range ((g⁻¹ : GL n 𝔸ᶠ[E]) : Matrix n n 𝔸ᶠ[E]).col)).toAddSubgroup.relIndex
          (Submodule.span (integralAdeles (𝓞 E) E)
            (Set.range (1 : Matrix n n 𝔸ᶠ[E]).col)).toAddSubgroup := by
  rw [← h.span_col_eq, genIndex_det_eq_relIndex h.val_mem]

/-! ### The multiplier -/

/-- The determinant of an element of `GL_n(Ô)` is an integral unit. -/
private theorem det_map_mem_integralUnits (k : GL n (integralAdeles (𝓞 E) E)) :
    det (map (integralAdeles (𝓞 E) E).val.toRingHom k) ∈ integralUnits (𝓞 E) E := by
  rw [GeneralLinearGroup.map_det, ← range_units_map_val_eq_integralUnits]
  exact ⟨_, rfl⟩

/-- The **multiplier** of `g ∈ GL_n(𝔸_f)`: the class of `det u` modulo the integral units `Ô^×`,
for a saturating matrix `u` of `g` (`u` and `g u` integral, `u⁻¹ = l + m g` with `l`, `m`
integral). It does not depend on `u`
(`Matrix.GeneralLinearGroup.IsSaturating.glMultiplier_eq`), since `u Ôⁿ = Ôⁿ ∩ g⁻¹Ôⁿ` determines
`u` up to `GL_n(Ô)`. For a character `χ` of the finite ideles trivial on `Ô^×`, the multiplier
`Δ_χ(g) = χ(det u)` is the image of `glMultiplier g` under the character
`QuotientGroup.lift _ χ hχ` induced on the quotient
(`Matrix.GeneralLinearGroup.IsSaturating.lift_glMultiplier`). -/
def glMultiplier (g : GL n 𝔸ᶠ[E]) : 𝔸ᶠ[E]ˣ ⧸ integralUnits (𝓞 E) E :=
  (det (exists_isSaturating g).choose : 𝔸ᶠ[E]ˣ)

/-- The multiplier of `g` is the class of `det u` for every saturating matrix `u` of `g`. -/
theorem _root_.Matrix.GeneralLinearGroup.IsSaturating.glMultiplier_eq {g u : GL n 𝔸ᶠ[E]}
    (h : IsSaturating (integralAdeles (𝓞 E) E) g u) :
    glMultiplier g = (det u : 𝔸ᶠ[E]ˣ ⧸ integralUnits (𝓞 E) E) := by
  obtain ⟨k, rfl⟩ := (exists_isSaturating g).choose_spec.exists_eq_mul_map h
  rw [glMultiplier, map_mul, QuotientGroup.mk_mul_of_mem _ (det_map_mem_integralUnits k)]

/-- **The multiplier of a character.** For a character `χ` of the finite ideles trivial on the
integral units, `Δ_χ(g) = χ(det u)` for every saturating matrix `u` of `g`: the value does not
depend on `u`. -/
theorem _root_.Matrix.GeneralLinearGroup.IsSaturating.lift_glMultiplier {M : Type*} [Monoid M]
    {χ : 𝔸ᶠ[E]ˣ →* M} (hχ : integralUnits (𝓞 E) E ≤ χ.ker) {g u : GL n 𝔸ᶠ[E]}
    (h : IsSaturating (integralAdeles (𝓞 E) E) g u) :
    QuotientGroup.lift _ χ hχ (glMultiplier g) = χ (det u) := by
  rw [h.glMultiplier_eq, QuotientGroup.lift_mk]

/-- **Bi-invariance.** `Δ(k g k') = Δ(g)` for `k`, `k' ∈ GL_n(Ô)`. -/
theorem glMultiplier_map_mul_mul_map (k k' : GL n (integralAdeles (𝓞 E) E)) (g : GL n 𝔸ᶠ[E]) :
    glMultiplier (map (integralAdeles (𝓞 E) E).val.toRingHom k * g *
      map (integralAdeles (𝓞 E) E).val.toRingHom k') = glMultiplier g := by
  obtain ⟨u, hu⟩ := exists_isSaturating g
  rw [(hu.map_mul_mul_map k k').glMultiplier_eq, hu.glMultiplier_eq, map_mul, mul_comm,
    ← GeneralLinearGroup.map_inv, QuotientGroup.mk_mul_of_mem _ (det_map_mem_integralUnits k'⁻¹)]

/-- The multiplier of an integral matrix is `1`. -/
theorem glMultiplier_eq_one_of_mem {g : GL n 𝔸ᶠ[E]}
    (hg : (g : Matrix n n 𝔸ᶠ[E]) ∈ (integralAdeles (𝓞 E) E).matrix) : glMultiplier g = 1 := by
  rw [(isSaturating_one_of_mem hg).glMultiplier_eq, map_one, QuotientGroup.mk_one]

/-- **The multiplier of the inverse.** `Δ(g⁻¹) = det g · Δ(g)`. -/
theorem glMultiplier_inv (g : GL n 𝔸ᶠ[E]) :
    glMultiplier g⁻¹ = (det g : 𝔸ᶠ[E]ˣ ⧸ integralUnits (𝓞 E) E) * glMultiplier g := by
  obtain ⟨u, hu⟩ := exists_isSaturating g
  rw [hu.inv.glMultiplier_eq, hu.glMultiplier_eq, map_mul, QuotientGroup.mk_mul]

/-- `x` lies in `δ Ô` exactly when `δ⁻¹ x` is integral, for a finite idele `δ`. -/
private theorem mem_span_singleton_iff (δ : 𝔸ᶠ[E]ˣ) {x : 𝔸ᶠ[E]} :
    x ∈ Submodule.span (integralAdeles (𝓞 E) E) {(δ : 𝔸ᶠ[E])} ↔
      ((δ⁻¹ : 𝔸ᶠ[E]ˣ) : 𝔸ᶠ[E]) * x ∈ integralAdeles (𝓞 E) E := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    simp [Subalgebra.smul_def, ← mul_assoc, mul_comm _ (c : 𝔸ᶠ[E])]
  · intro h
    exact ⟨⟨_, h⟩, by simp [Subalgebra.smul_def, mul_comm, ← mul_assoc]⟩

/-- **The multiplier through elementary divisors.** For `k`, `k' ∈ GL_n(Ô)` and a diagonal matrix
`d`, `Δ(k d k') = ∏ᵢ δᵢ` whenever `δᵢ Ô = Ô ∩ dᵢ⁻¹ Ô` for every `i`. -/
theorem glMultiplier_map_mul_diagGL_mul_map (k k' : GL n (integralAdeles (𝓞 E) E))
    {d δ : n → 𝔸ᶠ[E]ˣ}
    (hδ : ∀ i, Submodule.span (integralAdeles (𝓞 E) E) {(δ i : 𝔸ᶠ[E])} =
      Submodule.span (integralAdeles (𝓞 E) E) {1} ⊓
        Submodule.span (integralAdeles (𝓞 E) E) {(((d i)⁻¹ : 𝔸ᶠ[E]ˣ) : 𝔸ᶠ[E])}) :
    glMultiplier (map (integralAdeles (𝓞 E) E).val.toRingHom k * TauCeti.diagGL d *
      map (integralAdeles (𝓞 E) E).val.toRingHom k') =
        ∏ i, (δ i : 𝔸ᶠ[E]ˣ ⧸ integralUnits (𝓞 E) E) := by
  -- `diagGL δ` is saturating for `diagGL d`: its columns span `Ôⁿ ∩ (diagGL d)⁻¹ Ôⁿ`.
  have hsat : IsSaturating (integralAdeles (𝓞 E) E) (TauCeti.diagGL d) (TauCeti.diagGL δ) := by
    rw [isSaturating_iff_span_col_eq]
    ext x
    rw [Submodule.mem_inf, mem_span_col_one_iff, mem_span_col_iff_mulVec_inv_mem,
      mem_span_col_iff_mulVec_inv_mem, inv_inv, ← map_inv, TauCeti.diagGL_coe,
      TauCeti.diagGL_coe]
    simp only [mulVec_diagonal, ← forall_and]
    refine forall_congr' fun i ↦ ?_
    have h := SetLike.ext_iff.1 (hδ i) (x i)
    have h_one := mem_span_singleton_iff (E := E) 1 (x := x i)
    rw [Units.val_one, inv_one, Units.val_one, one_mul] at h_one
    rw [Submodule.mem_inf, mem_span_singleton_iff, mem_span_singleton_iff, inv_inv, h_one] at h
    simpa using h
  rw [glMultiplier_map_mul_mul_map, hsat.glMultiplier_eq, ← QuotientGroup.mk_prod]
  congr 1
  ext
  simp

/-- **Multiplicativity on block-diagonal matrices.** -/
theorem glMultiplier_fromBlocksGL {m : Type*} [Fintype m] [DecidableEq m] (g₁ : GL n 𝔸ᶠ[E])
    (g₂ : GL m 𝔸ᶠ[E]) :
    glMultiplier (TauCeti.fromBlocksGL (g₁, g₂)) = glMultiplier g₁ * glMultiplier g₂ := by
  obtain ⟨u₁, hu₁⟩ := exists_isSaturating g₁
  obtain ⟨u₂, hu₂⟩ := exists_isSaturating g₂
  rw [(hu₁.fromBlocksGL hu₂).glMultiplier_eq, hu₁.glMultiplier_eq, hu₂.glMultiplier_eq,
    ← QuotientGroup.mk_mul]
  congr 1
  ext
  simp [val_det_apply, det_fromBlocks_zero₂₁]

/-- **Multiplicativity along complementary idempotents.** For an idempotent `e` of `𝔸_f`, the
multiplier of `a b`, where `a` is `g₁` along `e` and `1` along `1 - e` and `b` is `1` along `e` and
`g₂` along `1 - e`, is `Δ(a) Δ(b)`. For the idempotent `e` that is `1` at the places of a set `S`
and `0` elsewhere, this is multiplicativity on products of a matrix supported at `S` and one
supported off `S`. -/
theorem glMultiplier_cutGL_mul_cutGL {e : 𝔸ᶠ[E]} (he : IsIdempotentElem e) (g₁ g₂ : GL n 𝔸ᶠ[E]) :
    glMultiplier (he.cutGL g₁ * he.one_sub.cutGL g₂) =
      glMultiplier (he.cutGL g₁) * glMultiplier (he.one_sub.cutGL g₂) := by
  obtain ⟨u₁, hu₁⟩ := exists_isSaturating g₁
  obtain ⟨u₂, hu₂⟩ := exists_isSaturating g₂
  have heS := mem_integralAdeles_of_isIdempotentElem he
  have h_one : IsSaturating (integralAdeles (𝓞 E) E) (1 : GL n 𝔸ᶠ[E]) 1 :=
    isSaturating_one_of_mem (by rw [Units.val_one]; exact one_mem _)
  have h₁ := hu₁.cutGL_mul_cutGL he heS h_one
  have h₂ := h_one.cutGL_mul_cutGL he heS hu₂
  simp only [map_one, mul_one, one_mul] at h₁ h₂
  rw [(hu₁.cutGL_mul_cutGL he heS hu₂).glMultiplier_eq, h₁.glMultiplier_eq, h₂.glMultiplier_eq,
    map_mul, QuotientGroup.mk_mul]

end NumberField.FiniteAdeleRing
