/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Hom
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Radical

/-!
# Kernels and images of right multiplication between zigzag vertex projectives

For a finite simple graph without isolated vertices, a homomorphism between vertex projectives
`P_j = Z e_j → P_i = Z e_i` of the zigzag relation quotient is right multiplication by an element
of the corner `e_j Z e_i`.  This file computes the kernel and the image, in terms of the radical
filtration `P_i ⊇ J P_i ⊇ J² P_i ⊇ 0`, of the two kinds of homogeneous maps of positive degree:

* right multiplication by the volume class `x_i`, an endomorphism of `P_i` of degree two, has
  image the socle `J² P_i` and kernel the radical `J P_i`, at every vertex; and
* right multiplication by the arrow of a dart `d`, a map `P_{d.snd} → P_{d.fst}` of degree one,
  always has image in `J P_{d.fst}` and kills `J² P_{d.snd}`.  Its image is all of `J P_{d.fst}`
  when the tail `d.fst` has degree one, and its kernel is exactly `J² P_{d.snd}` when the head
  `d.snd` has degree one.

Together with the quotient `P_i → P_i / J P_i` onto the simple head, whose kernel is `J P_i`,
these are the exactness statements behind the explicit projective resolutions of the simple
modules of low-rank zigzag algebras.

## Main definitions

* `TauCeti.zigzagProjectiveVolumeMul`: right multiplication by `x_i` on `P_i`.
* `TauCeti.zigzagProjectiveArrowMul`: right multiplication by the arrow of `d`,
  `P_{d.snd} → P_{d.fst}`.
* `TauCeti.zigzagProjectiveToHead`: the quotient of `P_i` onto its head `P_i / J P_i`.

## Main results

* `TauCeti.range_zigzagProjectiveVolumeMul` and `TauCeti.ker_zigzagProjectiveVolumeMul`: the
  image `J² P_i` and the kernel `J P_i` of the volume map.
* `TauCeti.range_zigzagProjectiveArrowMul` and `TauCeti.ker_zigzagProjectiveArrowMul`: the image
  `J P_{d.fst}` and the kernel `J² P_{d.snd}` of the arrow map, at vertices of degree one.
* `TauCeti.ker_zigzagProjectiveToHead`: the kernel `J P_i` of the head quotient.

## References

See Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, for the
projective modules of zigzag algebras and the maps between them.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => nonisolatedZigzagQuotient k G

/-! ### The maps -/

/-- Right multiplication by the volume class `x_i`, as an endomorphism of the vertex projective
`P_i = Z e_i`. -/
noncomputable def zigzagProjectiveVolumeMul (i : V) :
    zigzagProjective k G i →ₗ[Z] zigzagProjective k G i :=
  (zigzagProjectiveHomEquivCorner k G i i).symm
    ⟨zigzagVolume k G i, zigzagVolume_mem_zigzagCorner k G i⟩

@[simp]
theorem coe_zigzagProjectiveVolumeMul_apply (i : V) (y : zigzagProjective k G i) :
    (zigzagProjectiveVolumeMul k G i y : Z) = y * zigzagVolume k G i :=
  coe_zigzagProjectiveHomEquivCorner_symm_apply k G _ y

/-- Right multiplication by the arrow of a dart `d`, as a homomorphism of vertex projectives
`P_{d.snd} → P_{d.fst}`. -/
noncomputable def zigzagProjectiveArrowMul (d : G.Dart) :
    zigzagProjective k G d.snd →ₗ[Z] zigzagProjective k G d.fst :=
  (zigzagProjectiveHomEquivCorner k G d.snd d.fst).symm
    ⟨zigzagMk k G (ofArrow (arrow G d.adj)), zigzagMk_ofArrow_mem_zigzagCorner k G d⟩

@[simp]
theorem coe_zigzagProjectiveArrowMul_apply (d : G.Dart) (y : zigzagProjective k G d.snd) :
    (zigzagProjectiveArrowMul k G d y : Z) = y * zigzagMk k G (ofArrow (arrow G d.adj)) :=
  coe_zigzagProjectiveHomEquivCorner_symm_apply k G _ y

/-- Right multiplication by an arrow raises the path degree by one. With the source shifted
by one, this is a degree-zero map in a linear projective presentation. -/
theorem zigzagProjectiveArrowMul_mem_grade (d : G.Dart) {p : ℤ}
    {x : zigzagProjective k G d.snd} (hx : x ∈ zigzagProjectiveGrade k G d.snd p) :
    zigzagProjectiveArrowMul k G d x ∈ zigzagProjectiveGrade k G d.fst (p + 1) := by
  rw [mem_zigzagProjectiveGrade_iff, coe_zigzagProjectiveArrowMul_apply]
  have ha : zigzagMk k G (ofArrow (arrow G d.adj)) ∈ zigzagIntegerGrade k G 1 := by
    -- Present the integer numeral as a natural-number cast for the extension-by-zero API.
    rw [show (1 : ℤ) = (1 : ℕ) from rfl, zigzagIntegerGrade_ofNat]
    exact zigzagMk_mem_zigzagGrade k G (PathAlgebra.ofArrow_mem_grade_one _)
  exact mul_mem_zigzagIntegerGrade k G ((mem_zigzagProjectiveGrade_iff k G).1 hx) ha

/-- An arrow map after the volume map at its source vanishes: `x_{d.snd} a_d` has path length
three. -/
@[simp]
theorem zigzagProjectiveArrowMul_comp_zigzagProjectiveVolumeMul (d : G.Dart) :
    zigzagProjectiveArrowMul k G d ∘ₗ zigzagProjectiveVolumeMul k G d.snd = 0 :=
  LinearMap.ext fun y => Subtype.ext <| by
    rw [LinearMap.comp_apply, coe_zigzagProjectiveArrowMul_apply,
      coe_zigzagProjectiveVolumeMul_apply, mul_assoc, zigzagVolume_mul_zigzagMk_ofArrow,
      mul_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero]

/-- The volume map at the target of an arrow map, after it, vanishes: `a_d x_{d.fst}` has path
length three. -/
@[simp]
theorem zigzagProjectiveVolumeMul_comp_zigzagProjectiveArrowMul (d : G.Dart) :
    zigzagProjectiveVolumeMul k G d.fst ∘ₗ zigzagProjectiveArrowMul k G d = 0 :=
  LinearMap.ext fun y => Subtype.ext <| by
    rw [LinearMap.comp_apply, coe_zigzagProjectiveVolumeMul_apply,
      coe_zigzagProjectiveArrowMul_apply, mul_assoc, zigzagMk_ofArrow_mul_zigzagVolume,
      mul_zero, LinearMap.zero_apply, ZeroMemClass.coe_zero]

/-- The quotient of the vertex projective `P_i` onto its head `P_i / J P_i`, the radical layer
`TauCeti.zigzagProjectiveRadicalLayer k G i 0`. -/
noncomputable def zigzagProjectiveToHead (i : V) :
    zigzagProjective k G i →ₗ[Z] zigzagProjectiveRadicalLayer k G i 0 :=
  ((zigzagProjectiveRadicalPower k G i 1).submoduleOf
      (zigzagProjectiveRadicalPower k G i 0)).mkQ ∘ₗ
    LinearMap.codRestrict (zigzagProjectiveRadicalPower k G i 0) LinearMap.id (by simp)

/-- The head quotient is onto. -/
theorem zigzagProjectiveToHead_surjective (i : V) :
    Function.Surjective (zigzagProjectiveToHead k G i) := by
  rintro ⟨x, hx⟩
  exact ⟨x, rfl⟩

variable {k G}

/-- The head quotient sends `y ∈ P_i = J⁰ P_i` to its class modulo `J P_i`. -/
@[simp]
theorem zigzagProjectiveToHead_apply (i : V) (y : zigzagProjective k G i) :
    zigzagProjectiveToHead k G i y = Submodule.Quotient.mk ⟨y, by simp⟩ :=
  (rfl)

/-- **The kernel of the head quotient is the radical `J P_i`.** -/
@[simp]
theorem ker_zigzagProjectiveToHead (i : V) :
    LinearMap.ker (zigzagProjectiveToHead k G i) = zigzagProjectiveRadicalPower k G i 1 := by
  ext x
  rw [LinearMap.mem_ker, zigzagProjectiveToHead, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap,
    Submodule.subtype_apply, LinearMap.codRestrict_apply, LinearMap.id_apply]

/-! ### Radical bookkeeping -/

variable (hns : ∀ i : V, ∃ j, G.Adj i j)
include hns

private theorem zigzagMk_ofArrow_mem_jacobson (d : G.Dart) :
    zigzagMk k G (ofArrow (arrow G d.adj)) ∈ Ring.jacobson Z := by
  have h := zigzagMk_ofArrow_mem_zigzagPositiveSpan (k := k) d
  rwa [← restrictScalars_jacobson_nonisolatedZigzagQuotient_eq_zigzagPositiveSpan hns] at h

/-- A product of an element of `J^m` and an element of `J^n` vanishes when `m + n = 3`. -/
private theorem mul_eq_zero_of_mem_jacobson_pow {m n : ℕ} (hmn : m + n = 3) (hn : n ≠ 0)
    {x y : Z} (hx : x ∈ Ring.jacobson Z ^ m) (hy : y ∈ Ring.jacobson Z ^ n) : x * y = 0 := by
  have h : x * y ∈ Ring.jacobson Z ^ (m + n) := by
    rw [Submodule.pow_add _ hn]
    exact Ideal.mul_mem_mul hx hy
  rwa [hmn, jacobson_pow_three_nonisolatedZigzagQuotient_eq_bot hns, Ideal.mem_bot] at h

/-! ### The volume map -/

/-- **The image of the volume map is the socle `J² P_i`.** -/
@[simp]
theorem range_zigzagProjectiveVolumeMul (i : V) :
    LinearMap.range (zigzagProjectiveVolumeMul k G i) = zigzagProjectiveRadicalPower k G i 2 := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_zigzagProjectiveRadicalPower_iff, coe_zigzagProjectiveVolumeMul_apply]
    exact (Ring.jacobson Z ^ 2).mul_mem_left _ (zigzagVolume_mem_jacobson_sq hns i)
  · intro x hx
    have hx' : x ∈ (zigzagProjectiveRadicalPower k G i 2).restrictScalars k := hx
    rw [restrictScalars_zigzagProjectiveRadicalPower_two_eq_volumeLine hns,
      mem_zigzagProjectiveVolumeLine_iff] at hx'
    obtain ⟨c, rfl⟩ := hx'
    refine ⟨c • zigzagProjectiveGenerator k G i, Subtype.ext ?_⟩
    rw [coe_zigzagProjectiveVolumeMul_apply, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower, coe_zigzagProjectiveGenerator, coe_zigzagProjectiveVolume,
      smul_mul_assoc, zigzagVertexIdempotent, zigzagMk_vertexIdempotent_mul_zigzagVolume]

/-- **The kernel of the volume map is the radical `J P_i`.** -/
@[simp]
theorem ker_zigzagProjectiveVolumeMul (i : V) :
    LinearMap.ker (zigzagProjectiveVolumeMul k G i) = zigzagProjectiveRadicalPower k G i 1 := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hy' := congrArg Subtype.val hy
    rw [coe_zigzagProjectiveVolumeMul_apply, mul_zigzagVolume hns, ZeroMemClass.coe_zero,
      smul_eq_zero] at hy'
    obtain ⟨j, hij⟩ := hns i
    have hcoeff : zigzagProjectiveHeadCoeff k G i y = 0 := by
      rw [zigzagProjectiveHeadCoeff_apply, zigzagTrivialCoeff_apply_eq_repr hns]
      exact hy'.resolve_right (zigzagVolume_ne_zero k G hij)
    have hmem : y ∈ LinearMap.ker (zigzagProjectiveHeadCoeff k G i) := hcoeff
    rw [ker_zigzagProjectiveHeadCoeff_eq_restrictScalars_radicalPower_one hns] at hmem
    exact hmem
  · intro y hy
    rw [mem_zigzagProjectiveRadicalPower_iff, Submodule.pow_one] at hy
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    rw [coe_zigzagProjectiveVolumeMul_apply, ZeroMemClass.coe_zero]
    exact mul_eq_zero_of_mem_jacobson_pow hns (m := 1) (n := 2) rfl two_ne_zero
      (by rwa [Submodule.pow_one]) (zigzagVolume_mem_jacobson_sq hns i)

/-! ### The arrow map -/

/-- The image of an arrow map lies in the radical of its target. -/
theorem range_zigzagProjectiveArrowMul_le (d : G.Dart) :
    LinearMap.range (zigzagProjectiveArrowMul k G d) ≤
      zigzagProjectiveRadicalPower k G d.fst 1 := by
  rintro _ ⟨y, rfl⟩
  rw [mem_zigzagProjectiveRadicalPower_iff, coe_zigzagProjectiveArrowMul_apply,
    Submodule.pow_one]
  exact (Ring.jacobson Z).mul_mem_left _ (zigzagMk_ofArrow_mem_jacobson hns d)

/-- An arrow map kills the socle of its source. -/
theorem zigzagProjectiveRadicalPower_two_le_ker_zigzagProjectiveArrowMul (d : G.Dart) :
    zigzagProjectiveRadicalPower k G d.snd 2 ≤ LinearMap.ker (zigzagProjectiveArrowMul k G d) := by
  intro y hy
  rw [mem_zigzagProjectiveRadicalPower_iff] at hy
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  rw [coe_zigzagProjectiveArrowMul_apply, ZeroMemClass.coe_zero]
  exact mul_eq_zero_of_mem_jacobson_pow hns (m := 2) (n := 1) rfl one_ne_zero hy
    (by rw [Submodule.pow_one]; exact zigzagMk_ofArrow_mem_jacobson hns d)

omit hns in
private theorem finiteDimensional_zigzagProjective (hns : ∀ i : V, ∃ j, G.Adj i j) (i : V) :
    FiniteDimensional k (zigzagProjective k G i) := by
  classical
  let _ := Fintype.ofFinite V
  exact Module.Finite.of_basis (zigzagProjectiveBasis k G hns i)

/-- The image of an arrow map is at least two-dimensional: it contains the arrow itself, the
image of `e_{d.snd}`, and the volume class `x_{d.fst}`, the image of the reverse arrow. -/
private theorem two_le_finrank_range_zigzagProjectiveArrowMul (d : G.Dart) :
    2 ≤ Module.finrank k
      ((LinearMap.range (zigzagProjectiveArrowMul k G d)).restrictScalars k) := by
  have := finiteDimensional_zigzagProjective (k := k) hns d.fst
  let b := zigzagProjectiveBasis k G hns d.fst
  let ι : Fin 2 → ZigzagProjectiveBasisIndex G d.fst := ![.inr (.inl ⟨d, rfl⟩), .inr (.inr ())]
  have hι : Function.Injective ι := by
    intro a a' h
    fin_cases a <;> fin_cases a' <;> simp_all [ι]
  have hli : LinearIndependent k (b ∘ ι) := b.linearIndependent.comp ι hι
  have hle : Submodule.span k (Set.range (b ∘ ι)) ≤
      (LinearMap.range (zigzagProjectiveArrowMul k G d)).restrictScalars k := by
    rw [Submodule.span_le, Set.range_subset_iff]
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · refine ⟨zigzagProjectiveGenerator k G d.snd, Subtype.ext ?_⟩
      simp only [coe_zigzagProjectiveArrowMul_apply, coe_zigzagProjectiveGenerator,
        Function.comp_apply, b, ι, zigzagProjectiveBasis_apply, Matrix.cons_val_zero,
        coe_zigzagProjectiveBasisFun_inr_inl]
      exact zigzagMk_vertexIdempotent_mul_ofArrow k G d
    · let r : zigzagProjective k G d.snd :=
        zigzagProjectiveBasisFun k G d.snd (.inr (.inl ⟨d.symm, rfl⟩))
      refine ⟨r, Subtype.ext ?_⟩
      have h := zigzagMk_ofArrow_mul_ofArrow_symm k G d.symm
      simp only [SimpleGraph.Dart.symm_toProd, Prod.snd_swap] at h
      simp only [coe_zigzagProjectiveArrowMul_apply, r, coe_zigzagProjectiveBasisFun_inr_inl,
        Function.comp_apply, b, ι, zigzagProjectiveBasis_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, coe_zigzagProjectiveBasisFun_inr_inr]
      exact h
  calc 2 = Module.finrank k (Submodule.span k (Set.range (b ∘ ι))) := by
        rw [finrank_span_eq_card hli, Fintype.card_fin]
    _ ≤ _ := Submodule.finrank_mono hle

/-- The head quotient at `d.fst` kills the image of the arrow map of `d`. -/
@[simp]
theorem zigzagProjectiveToHead_comp_zigzagProjectiveArrowMul (d : G.Dart) :
    zigzagProjectiveToHead k G d.fst ∘ₗ zigzagProjectiveArrowMul k G d = 0 := by
  ext y
  rw [LinearMap.comp_apply, LinearMap.zero_apply, ← LinearMap.mem_ker,
    ker_zigzagProjectiveToHead]
  exact range_zigzagProjectiveArrowMul_le hns d (LinearMap.mem_range_self _ y)

section Finite

variable [Fintype V] [DecidableRel G.Adj]

/-- **At a tail of degree one, the image of an arrow map is the radical `J P_{d.fst}`.** -/
@[simp]
theorem range_zigzagProjectiveArrowMul (d : G.Dart) (hd : G.degree d.fst = 1) :
    LinearMap.range (zigzagProjectiveArrowMul k G d) =
      zigzagProjectiveRadicalPower k G d.fst 1 := by
  have := finiteDimensional_zigzagProjective (k := k) hns d.fst
  apply Submodule.restrictScalars_injective k
  apply Submodule.eq_of_le_of_finrank_le
  · exact range_zigzagProjectiveArrowMul_le hns d
  · have h := finrank_restrictScalars_zigzagProjectiveRadicalPower_one hns (k := k) d.fst
    rw [hd] at h
    -- The `k`-structure on the radical is the one of its restriction of scalars.
    change Module.finrank k (zigzagProjectiveRadicalPower k G d.fst 1) ≤ _
    rw [h]
    exact two_le_finrank_range_zigzagProjectiveArrowMul (k := k) hns d

/-- **At a head of degree one, the kernel of an arrow map is the socle `J² P_{d.snd}`.** -/
@[simp]
theorem ker_zigzagProjectiveArrowMul (d : G.Dart) (hd : G.degree d.snd = 1) :
    LinearMap.ker (zigzagProjectiveArrowMul k G d) =
      zigzagProjectiveRadicalPower k G d.snd 2 := by
  have := finiteDimensional_zigzagProjective (k := k) hns d.snd
  apply Submodule.restrictScalars_injective k
  symm
  apply Submodule.eq_of_le_of_finrank_le
  · exact zigzagProjectiveRadicalPower_two_le_ker_zigzagProjectiveArrowMul hns d
  · have hrank := LinearMap.finrank_range_add_finrank_ker
      ((zigzagProjectiveArrowMul k G d).restrictScalars k)
    rw [LinearMap.range_restrictScalars, LinearMap.ker_restrictScalars,
      finrank_zigzagProjective k G hns, hd] at hrank
    have h2 := two_le_finrank_range_zigzagProjectiveArrowMul (k := k) hns d
    have h1 := finrank_restrictScalars_zigzagProjectiveRadicalPower_two hns (k := k) d.snd
    -- The `k`-structure on the socle is the one of its restriction of scalars.
    change _ ≤ Module.finrank k (zigzagProjectiveRadicalPower k G d.snd 2)
    omega

end Finite

end TauCeti
