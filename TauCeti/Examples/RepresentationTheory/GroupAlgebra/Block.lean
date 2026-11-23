/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Lift
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.ScalarExtension

/-!
# Examples of block idempotents of group algebras

Block idempotents (`TauCeti.IsBlockIdempotent`) of small group algebras, computed by hand.

* **`𝔽₂[C₂]`**: `1` is the only block idempotent; `ε = 1 + t` satisfies `ε² = 0`, so
  `𝔽₂[C₂] ≅ 𝔽₂[ε]/(ε²)` and `ε` is not idempotent.
* **`𝔽₃[C₂]`**: `e₊ = -(1 + t)` and `e₋ = -(1 - t)`, that is `(1 ± t)/2`, are block idempotents;
  their sum `1` is a central idempotent which is not primitive.
* **`𝔽₂[C₃]` and `K[C₃]`**: `1 + r + r²` and `r + r²` are blocks of `𝔽₂[C₃]`. Over a field `K`
  of characteristic `2` containing a root `α` of `X² + X + 1`, for instance `𝔽₄`, the image of
  `r + r²` is the sum of the two blocks `1 + α² r + α r²` and `1 + α r + α² r²` of `K[C₃]`, so
  scalar extension does not preserve primitivity.
* **`𝔽₂[S₃]` and `𝔽₃[S₃]`**: `𝔽₂[S₃]` has the blocks `1 + ρ + ρ²` and `ρ + ρ²` (`ρ` a
  `3`-cycle), with sum `1` and product `0`; `1` is the only block of `𝔽₃[S₃]`.
* **Lifts to `ℤ₂`**: the only block of `ℤ₂[1]` is `1`, although the maximal ideal `(2)` of `ℤ₂`
  is not nilpotent; the blocks `1 + r + r²` and `r + r²` of `𝔽₂[C₃]` lift to the blocks
  `(1 + r + r²)/3` and `(2 - r - r²)/3` of `ℤ₂[C₃]`; the ordinary idempotents `(1 ± t)/2` are not
  in `ℤ₂[C₂]`, whose only block is `1`.

The finite computations go through a criterion on coefficient functions
(`TauCeti.GroupAlgebraBlockExamples.isBlockIdempotent_of_coeff`), which `decide` checks, and the
blocks whose block algebra is the coefficient field go through
`TauCeti.GroupAlgebraBlockExamples.isBlockIdempotent_of_mul_of_eq_smul`.
-/

public section

namespace TauCeti.GroupAlgebraBlockExamples

open MonoidAlgebra

/-! ### Criteria in terms of coefficients -/

section Criterion

variable {k G : Type*} [CommRing k] [Group G]

/-- The coefficients of a product in the group algebra of a finite group, as a convolution. -/
theorem coeff_mul_eq_sum [Fintype G] (x y : MonoidAlgebra k G) (g : G) :
    (x * y).coeff g = ∑ h, x.coeff h * y.coeff (h⁻¹ * g) := by
  rw [coeff_mul_apply_left, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _]

/-- The coefficients of a central element of a group algebra are constant on conjugacy classes. -/
theorem coeff_conj_of_mem_center {x : MonoidAlgebra k G}
    (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G)) (g h : G) :
    x.coeff (g * h * g⁻¹) = x.coeff h := by
  have := congr_arg (fun y ↦ y.coeff (g * h)) (Subalgebra.mem_center_iff.mp hx (single g 1))
  simpa [coeff_single_mul_apply, coeff_mul_single_apply] using this.symm

/-- An element of a group algebra whose coefficients are constant on conjugacy classes is
central. -/
theorem mem_center_of_coeff_conj {x : MonoidAlgebra k G}
    (hx : ∀ g h, x.coeff (g * h * g⁻¹) = x.coeff h) :
    x ∈ Subalgebra.center k (MonoidAlgebra k G) := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => rw [add_mul, mul_add, hy, hz]
  | single g r =>
    refine ext (Finsupp.ext fun h ↦ ?_)
    rw [coeff_single_mul_apply, coeff_mul_single_apply, mul_comm, ← hx g (g⁻¹ * h)]
    simp

/-- If `cls : G → ι` only identifies conjugate elements, the coefficients of a central element of
`k[G]` factor through `cls`. -/
theorem exists_coeff_eq_comp {ι : Type*} (cls : G → ι) (hcls : ∀ g h, cls g = cls h → IsConj g h)
    {x : MonoidAlgebra k G} (hx : x ∈ Subalgebra.center k (MonoidAlgebra k G)) :
    ∃ ψ : ι → k, ⇑x.coeff = ψ ∘ cls := by
  classical
  refine ⟨fun i ↦ x.coeff (Function.invFun cls i), funext fun g ↦ ?_⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (hcls _ _ (Function.invFun_eq ⟨g, rfl⟩))
  simp only [Function.comp_apply]
  rw [← coeff_conj_of_mem_center hx c (Function.invFun cls (cls g)), hc]

variable [Fintype G]

/-- **A block criterion on coefficients.** Let `cls : G → ι` identify only conjugate elements, so
that central elements are functions of `cls`. A central element `b` with coefficient function `χ`
is a block idempotent if `χ` is idempotent and nonzero for the convolution product and every
idempotent function `ψ ∘ cls` absorbed by `χ` is `0` or `χ`. For finite `G`, `ι` and `k` these
conditions are decidable. -/
theorem isBlockIdempotent_of_coeff {ι : Type*} (cls : G → ι)
    (hcls : ∀ g h, cls g = cls h → IsConj g h)
    {b : Subalgebra.center k (MonoidAlgebra k G)} {χ : G → k}
    (hb : ⇑(b : MonoidAlgebra k G).coeff = χ)
    (hidem : ∀ g, ∑ h, χ h * χ (h⁻¹ * g) = χ g) (hne : χ ≠ 0)
    (hprim : ∀ ψ : ι → k, (∀ g, ∑ h, ψ (cls h) * ψ (cls (h⁻¹ * g)) = ψ (cls g)) →
      (∀ g, ∑ h, χ h * ψ (cls (h⁻¹ * g)) = ψ (cls g)) → ψ ∘ cls = 0 ∨ ψ ∘ cls = χ) :
    IsBlockIdempotent b := by
  have hcoeff {x y z : Subalgebra.center k (MonoidAlgebra k G)} (h : x * y = z) (g : G) :
      ∑ h, (x : MonoidAlgebra k G).coeff h * (y : MonoidAlgebra k G).coeff (h⁻¹ * g) =
        (z : MonoidAlgebra k G).coeff g := by
    rw [← coeff_mul_eq_sum, ← Subalgebra.coe_mul, h]
  refine isPrimitiveIdempotent_of_eq_zero_or_eq ?_ ?_ fun f hf hbf _ ↦ ?_
  · refine Subtype.ext (ext (Finsupp.ext fun g ↦ ?_))
    rw [Subalgebra.coe_mul, coeff_mul_eq_sum, hb]
    exact hidem g
  · rintro rfl
    exact hne (hb ▸ rfl)
  · obtain ⟨ψ, hψ⟩ := exists_coeff_eq_comp cls hcls f.property
    have hf' (g : G) := hcoeff hf.eq g
    have hbf' (g : G) := hcoeff hbf g
    simp only [hψ, hb, Function.comp_apply] at hf' hbf'
    refine (hprim ψ hf' hbf').imp (fun h0 ↦ ?_) fun h1 ↦ ?_
    · exact Subtype.ext (ext (DFunLike.coe_injective (hψ.trans h0)))
    · exact Subtype.ext (ext (DFunLike.coe_injective (hψ.trans (h1.trans hb.symm))))

/-- **A uniqueness criterion on coefficients.** Let `cls : G → ι` identify only conjugate
elements. If every nonzero idempotent function `ψ ∘ cls` for the convolution product is the
coefficient function `χ` of a central element `c`, then every block idempotent of `k[G]` is
`c`. -/
theorem eq_of_isBlockIdempotent {ι : Type*} (cls : G → ι)
    (hcls : ∀ g h, cls g = cls h → IsConj g h)
    {c : Subalgebra.center k (MonoidAlgebra k G)} {χ : G → k}
    (hc : ⇑(c : MonoidAlgebra k G).coeff = χ)
    (h : ∀ ψ : ι → k, (∀ g, ∑ h, ψ (cls h) * ψ (cls (h⁻¹ * g)) = ψ (cls g)) →
      ψ ∘ cls ≠ 0 → ψ ∘ cls = χ)
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) : b = c := by
  obtain ⟨ψ, hψ⟩ := exists_coeff_eq_comp cls hcls b.property
  have hidem (g : G) : ∑ h, ψ (cls h) * ψ (cls (h⁻¹ * g)) = ψ (cls g) := by
    have := hb.isIdempotentElem_val
    rw [IsIdempotentElem, ← coeff_inj] at this
    have := DFunLike.congr_fun this g
    simpa only [coeff_mul_eq_sum, hψ, Function.comp_apply] using this
  have hne : ψ ∘ cls ≠ 0 := fun h0 ↦ hb.ne_zero <| Subtype.ext <| ext <|
    DFunLike.coe_injective (hψ.trans h0)
  exact Subtype.ext (ext (DFunLike.coe_injective (hψ.trans ((h ψ hidem hne).trans hc.symm))))

/-- If `b * g = c(g) b` for every `g ∈ G`, then `b * x = (∑ g, x(g) c(g)) • b` for every `x`. -/
theorem mul_eq_smul_of_mul_of_eq_smul {b : MonoidAlgebra k G} {c : G → k}
    (hc : ∀ g, b * of k G g = c g • b) (x : MonoidAlgebra k G) :
    b * x = (∑ g, x.coeff g * c g) • b := by
  classical
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [mul_add, hx, hy, add_mul, add_smul, Finset.sum_add_distrib]
  | single g r =>
    have : single g r = r • of k G g := by simp [smul_single]
    rw [this, mul_smul_comm, hc, smul_smul]
    simp [Finsupp.single_apply]

/-- **Blocks with one-dimensional block algebra.** Over a domain `k`, a central element `b` with
`b g = c(g) b` for every `g`, coefficient `1` at the identity and `∑ g, b(g) c(g) = 1` is a block
idempotent: the block algebra `b k[G]` is the line `k b`. -/
theorem isBlockIdempotent_of_mul_of_eq_smul [IsDomain k]
    {b : Subalgebra.center k (MonoidAlgebra k G)} (c : G → k)
    (hc : ∀ g, (b : MonoidAlgebra k G) * of k G g = c g • (b : MonoidAlgebra k G))
    (h1 : (b : MonoidAlgebra k G).coeff 1 = 1)
    (hsum : ∑ g, (b : MonoidAlgebra k G).coeff g * c g = 1) : IsBlockIdempotent b := by
  have key := mul_eq_smul_of_mul_of_eq_smul hc
  have hbb : (b : MonoidAlgebra k G) * b = b := by rw [key, hsum, one_smul]
  refine isPrimitiveIdempotent_of_eq_zero_or_eq (Subtype.ext hbb) ?_ fun f hf hbf _ ↦ ?_
  · rintro rfl
    simp at h1
  · set s := ∑ g, (f : MonoidAlgebra k G).coeff g * c g
    have hfs : (f : MonoidAlgebra k G) = s • (b : MonoidAlgebra k G) := by
      rw [← key, ← Subalgebra.coe_mul, hbf]
    have hss : IsIdempotentElem s := by
      have h := congr_arg (fun y : Subalgebra.center k (MonoidAlgebra k G) ↦
        (y : MonoidAlgebra k G).coeff 1) hf.eq
      simp only [Subalgebra.coe_mul, hfs, smul_mul_smul_comm, hbb, coeff_smul_apply, h1,
        smul_eq_mul, mul_one] at h
      exact h
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hss with h0 | h1
    · exact .inl (Subtype.ext (by rw [hfs, h0, zero_smul]; rfl))
    · exact .inr (Subtype.ext (by rw [hfs, h1, one_smul]))

end Criterion

/-- `id` only identifies conjugate elements. -/
theorem isConj_of_id_eq {G : Type*} [Group G] (g h : G) (hgh : id g = id h) : IsConj g h :=
  (show g = h from hgh) ▸ IsConj.refl g

/-- An element of the group algebra of a commutative group, as an element of its centre. -/
def toCenter {k G : Type*} [CommRing k] [CommGroup G] (x : MonoidAlgebra k G) :
    Subalgebra.center k (MonoidAlgebra k G) :=
  ⟨x, Subalgebra.mem_center_iff.mpr fun y ↦ mul_comm y x⟩

/-- `toCenter x` is `x`, read in the group algebra. -/
@[simp]
theorem coe_toCenter {k G : Type*} [CommRing k] [CommGroup G] (x : MonoidAlgebra k G) :
    (toCenter x : MonoidAlgebra k G) = x := by
  simp [toCenter]

/-- An idempotent of the group algebra of a commutative group is an idempotent of its centre. -/
theorem isIdempotentElem_toCenter {k G : Type*} [CommRing k] [CommGroup G]
    {x : MonoidAlgebra k G} (hx : IsIdempotentElem x) : IsIdempotentElem (toCenter x) :=
  Subtype.ext (by rw [Subalgebra.coe_mul, coe_toCenter]; exact hx.eq)

/-! ### The cyclic group of order `2` -/

/-- The cyclic group `C₂` of order `2`. -/
abbrev C₂ : Type := Multiplicative (ZMod 2)

/-- The generator `t` of `C₂`. -/
abbrev t : C₂ := Multiplicative.ofAdd 1

/-- In `𝔽₂[C₂]` the element `ε = 1 + t` squares to `0`, so `𝔽₂[C₂] ≅ 𝔽₂[ε]/(ε²)`. -/
theorem one_add_of_t_mul_self :
    (1 + of (ZMod 2) C₂ t) * (1 + of (ZMod 2) C₂ t) = 0 := by
  refine ext (Finsupp.ext fun g ↦ ?_)
  simp only [coeff_mul_eq_sum, coeff_add, of_apply, one_def, coeff_single, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  revert g
  decide

/-- In `𝔽₂[C₂]` the element `ε = 1 + t` is nonzero. -/
theorem one_add_of_t_ne_zero : 1 + of (ZMod 2) C₂ t ≠ 0 := by
  intro h
  have := congr_arg (fun x : MonoidAlgebra (ZMod 2) C₂ ↦ x.coeff 1) h
  revert this
  simp only [coeff_add, of_apply, one_def, coeff_single, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  decide

/-- In `𝔽₂[C₂]` the element `ε = 1 + t` is not idempotent. -/
theorem not_isIdempotentElem_one_add_of_t : ¬ IsIdempotentElem (1 + of (ZMod 2) C₂ t) :=
  fun h ↦ one_add_of_t_ne_zero (h.eq.symm.trans one_add_of_t_mul_self)

/-- **`𝔽₂[C₂]` has a single block**: its only block idempotent is `1`. -/
theorem isBlockIdempotent_iff_eq_one_zmod_two_c₂
    (b : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) C₂)) :
    IsBlockIdempotent b ↔ b = 1 := by
  have hχ : ⇑((1 : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) C₂)) :
      MonoidAlgebra (ZMod 2) C₂).coeff = fun g ↦ if g = 1 then 1 else 0 := by
    funext g
    simp [one_def, Finsupp.single_apply, eq_comm]
  refine ⟨eq_of_isBlockIdempotent id isConj_of_id_eq hχ
    (by decide), ?_⟩
  rintro rfl
  exact isBlockIdempotent_of_coeff id isConj_of_id_eq hχ
    (by decide) (by decide) (by decide)

/-- The block idempotent `e₊ = -(1 + t)`, that is `(1 + t)/2`, of `𝔽₃[C₂]`. -/
noncomputable abbrev ePlus : MonoidAlgebra (ZMod 3) C₂ := -(1 + of (ZMod 3) C₂ t)

/-- The block idempotent `e₋ = -(1 - t)`, that is `(1 - t)/2`, of `𝔽₃[C₂]`. -/
noncomputable abbrev eMinus : MonoidAlgebra (ZMod 3) C₂ := -(1 - of (ZMod 3) C₂ t)

/-- `e₊ = (1 + t)/2` is a block idempotent of `𝔽₃[C₂]`. -/
theorem isBlockIdempotent_ePlus : IsBlockIdempotent (toCenter ePlus) := by
  refine isBlockIdempotent_of_coeff id isConj_of_id_eq (χ := fun _ ↦ 2) ?_ (by decide)
    (by decide) (by decide)
  funext g
  revert g
  simp only [coe_toCenter, coeff_neg, coeff_add, of_apply, one_def, coeff_single,
    Finsupp.coe_neg, Finsupp.coe_add, Pi.neg_apply, Pi.add_apply, Finsupp.single_apply]
  decide

/-- `e₋ = (1 - t)/2` is a block idempotent of `𝔽₃[C₂]`. -/
theorem isBlockIdempotent_eMinus : IsBlockIdempotent (toCenter eMinus) := by
  refine isBlockIdempotent_of_coeff id isConj_of_id_eq
    (χ := fun g ↦ if g = 1 then 2 else 1) ?_ (by decide) (by decide) (by decide)
  funext g
  revert g
  simp only [coe_toCenter, coeff_neg, coeff_sub, of_apply, one_def, coeff_single,
    Finsupp.coe_neg, Finsupp.coe_sub, Pi.neg_apply, Pi.sub_apply, Finsupp.single_apply]
  decide

/-- In `𝔽₃[C₂]` the blocks `e₊` and `e₋` form a complete orthogonal family of idempotents. -/
theorem completeOrthogonalIdempotents_ePlus_eMinus :
    CompleteOrthogonalIdempotents ![toCenter ePlus, toCenter eMinus] := by
  refine CompleteOrthogonalIdempotents.pair_iffₛ.mpr ⟨Subtype.ext (ext (Finsupp.ext fun g ↦ ?_)),
    Subtype.ext (ext (Finsupp.ext fun g ↦ ?_))⟩
  · revert g
    simp only [MulMemClass.coe_mul, coe_toCenter, coeff_mul_eq_sum, coeff_neg, coeff_sub, coeff_add,
      of_apply, one_def, coeff_single, Finsupp.coe_neg, Finsupp.coe_sub, Finsupp.coe_add,
      Pi.neg_apply, Pi.sub_apply, Pi.add_apply, Finsupp.single_apply, ZeroMemClass.coe_zero,
      coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    decide
  · revert g
    simp only [AddMemClass.coe_add, coe_toCenter, coeff_neg, coeff_sub, coeff_add, of_apply,
      one_def, coeff_single, Finsupp.coe_neg, Finsupp.coe_sub, Finsupp.coe_add, Pi.neg_apply,
      Pi.sub_apply, Pi.add_apply, Finsupp.single_apply, OneMemClass.coe_one]
    decide

/-- **`1` is not a block of `𝔽₃[C₂]`**: it is a central idempotent, the sum of the two
orthogonal block idempotents `e₊` and `e₋`, so it is not primitive. -/
theorem not_isBlockIdempotent_one_zmod_three_c₂ :
    ¬ IsBlockIdempotent (1 : Subalgebra.center (ZMod 3) (MonoidAlgebra (ZMod 3) C₂)) := by
  intro h
  have hc := completeOrthogonalIdempotents_ePlus_eMinus
  have hsum := hc.complete
  rw [Fin.sum_univ_two] at hsum
  rcases h.eq_zero_or_eq_zero_of_add (hc.idem 0) (hc.idem 1) (hc.ortho (by decide))
    (hc.ortho (by decide)) hsum with h0 | h0
  exacts [isBlockIdempotent_ePlus.ne_zero h0, isBlockIdempotent_eMinus.ne_zero h0]

/-! ### The cyclic group of order `3` -/

/-- The cyclic group `C₃` of order `3`. -/
abbrev C₃ : Type := Multiplicative (ZMod 3)

/-- The generator `r` of `C₃`. -/
abbrev r : C₃ := Multiplicative.ofAdd 1

/-- The block idempotent `1 + r + r²` of `𝔽₂[C₃]`. -/
theorem isBlockIdempotent_one_add_r_add_r_sq :
    IsBlockIdempotent (toCenter (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))) := by
  refine isBlockIdempotent_of_coeff id isConj_of_id_eq (χ := fun _ ↦ 1) ?_ (by decide)
    (by decide) (by decide)
  funext g
  revert g
  simp only [coe_toCenter, coeff_add, of_apply, one_def, coeff_single, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_apply]
  decide

/-- The block idempotent `r + r²` of `𝔽₂[C₃]`. -/
theorem isBlockIdempotent_r_add_r_sq :
    IsBlockIdempotent (toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))) := by
  refine isBlockIdempotent_of_coeff id isConj_of_id_eq (χ := fun g ↦ if g = 1 then 0 else 1) ?_
    (by decide) (by decide) (by decide)
  funext g
  revert g
  simp only [coe_toCenter, coeff_add, of_apply, coeff_single, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  decide

section ScalarExtension

variable {K : Type*} [Field K] {α : K}

/-- The block idempotent `1 + α² r + α r²` of `K[C₃]`, for a root `α` of `X² + X + 1`. -/
noncomputable abbrev eOne (α : K) : MonoidAlgebra K C₃ :=
  1 + α ^ 2 • of K C₃ r + α • of K C₃ (r ^ 2)

/-- The block idempotent `1 + α r + α² r²` of `K[C₃]`, for a root `α` of `X² + X + 1`. -/
noncomputable abbrev eTwo (α : K) : MonoidAlgebra K C₃ :=
  1 + α • of K C₃ r + α ^ 2 • of K C₃ (r ^ 2)

/-- Sums over `C₃`. -/
theorem sum_c₃ {M : Type*} [AddCommMonoid M] (f : C₃ → M) :
    ∑ g, f g = f 1 + f r + f (r ^ 2) := by
  rw [show (Finset.univ : Finset C₃) = {1, r, r ^ 2} by decide, Finset.sum_insert (by decide),
    Finset.sum_pair (by decide), add_assoc]

/-- A root of `X² + X + 1` is a cube root of unity. -/
theorem cube_eq_one (hα : α ^ 2 + α + 1 = 0) : α ^ 3 = 1 := by
  linear_combination (α - 1) * hα

/-- `r` acts on `1 + α² r + α r²` by `α`. -/
theorem eOne_mul_of (hα : α ^ 2 + α + 1 = 0) (g : C₃) :
    eOne α * of K C₃ g = (if g = 1 then 1 else if g = r then α else α ^ 2) • eOne α := by
  refine ext (Finsupp.ext fun h ↦ ?_)
  fin_cases g <;> fin_cases h <;>
    simp +decide [coeff_mul_single_apply, Finsupp.single_apply, one_def] <;>
    grind [cube_eq_one hα]

/-- `r` acts on `1 + α r + α² r²` by `α²`. -/
theorem eTwo_mul_of (hα : α ^ 2 + α + 1 = 0) (g : C₃) :
    eTwo α * of K C₃ g = (if g = 1 then 1 else if g = r then α ^ 2 else α) • eTwo α := by
  refine ext (Finsupp.ext fun h ↦ ?_)
  fin_cases g <;> fin_cases h <;>
    simp +decide [coeff_mul_single_apply, Finsupp.single_apply, one_def] <;>
    grind [cube_eq_one hα]

/-- The blocks `1 + α² r + α r²` and `1 + α r + α² r²` of `K[C₃]` are orthogonal. -/
theorem eOne_mul_eTwo (hα : α ^ 2 + α + 1 = 0) : eOne α * eTwo α = 0 := by
  rw [mul_eq_smul_of_mul_of_eq_smul (eOne_mul_of hα)]
  convert zero_smul K (eOne α)
  rw [sum_c₃]
  simp +decide [one_def]
  linear_combination (α ^ 2 - α + 1) * hα

variable [CharP K 2]

/-- Over a field of characteristic `2` containing a root `α` of `X² + X + 1`, for instance `𝔽₄`,
`1 + α² r + α r²` is a block idempotent of `K[C₃]`. -/
theorem isBlockIdempotent_eOne (hα : α ^ 2 + α + 1 = 0) : IsBlockIdempotent (toCenter (eOne α)) :=
  isBlockIdempotent_of_mul_of_eq_smul _ (eOne_mul_of hα) (by simp +decide [one_def]) <| by
    rw [sum_c₃]
    simp +decide [one_def]
    linear_combination α ^ 3 * CharTwo.two_eq_zero (R := K)

/-- Over a field of characteristic `2` containing a root `α` of `X² + X + 1`, for instance `𝔽₄`,
`1 + α r + α² r²` is a block idempotent of `K[C₃]`. -/
theorem isBlockIdempotent_eTwo (hα : α ^ 2 + α + 1 = 0) : IsBlockIdempotent (toCenter (eTwo α)) :=
  isBlockIdempotent_of_mul_of_eq_smul _ (eTwo_mul_of hα) (by simp +decide [one_def]) <| by
    rw [sum_c₃]
    simp +decide [one_def]
    linear_combination α ^ 3 * CharTwo.two_eq_zero (R := K)

/-- **Scalar extension splits a block.** Along `𝔽₂ → K`, for a field `K` of characteristic `2`
containing a root `α` of `X² + X + 1`, the block `r + r²` of `𝔽₂[C₃]` maps to the sum of the two
blocks `1 + α² r + α r²` and `1 + α r + α² r²` of `K[C₃]`. -/
theorem centerMapRingHom_r_add_r_sq (hα : α ^ 2 + α + 1 = 0) :
    centerMapRingHom C₃ (ZMod.castHom (dvd_refl 2) K)
        (toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2))) =
      toCenter (eOne α) + toCenter (eTwo α) := by
  refine Subtype.ext (ext (Finsupp.ext fun h ↦ ?_))
  fin_cases h <;>
    simp +decide [Finsupp.single_apply, one_def] <;> grind

/-- **Scalar extension does not preserve primitivity.** The image in `K[C₃]` of the block
`r + r²` of `𝔽₂[C₃]` is not a block idempotent. -/
theorem not_isBlockIdempotent_centerMapRingHom_r_add_r_sq (hα : α ^ 2 + α + 1 = 0) :
    ¬ IsBlockIdempotent (centerMapRingHom C₃ (ZMod.castHom (dvd_refl 2) K)
        (toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)))) := by
  rw [centerMapRingHom_r_add_r_sq hα]
  intro h
  have h₁₂ : toCenter (eOne α) * toCenter (eTwo α) = 0 := Subtype.ext (eOne_mul_eTwo hα)
  rcases h.eq_zero_or_eq_zero_of_add (isBlockIdempotent_eOne hα).isIdempotentElem
    (isBlockIdempotent_eTwo hα).isIdempotentElem h₁₂ (by rw [mul_comm, h₁₂]) rfl with h0 | h0
  exacts [(isBlockIdempotent_eOne hα).ne_zero h0, (isBlockIdempotent_eTwo hα).ne_zero h0]

end ScalarExtension

/-- `𝔽₄ = GaloisField 2 2` contains a root of `X² + X + 1`. -/
theorem exists_sq_add_self_add_one_eq_zero : ∃ α : GaloisField 2 2, α ^ 2 + α + 1 = 0 := by
  classical
  have hcard : Nat.card (GaloisField 2 2) = 4 := GaloisField.card 2 2 (by decide)
  have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  obtain ⟨α, hα0, hα1⟩ : ∃ α : GaloisField 2 2, α ≠ 0 ∧ α ≠ 1 := by
    by_contra! h
    have hsurj : Function.Surjective fun b : Bool ↦ if b then (1 : GaloisField 2 2) else 0 :=
      fun a ↦ (em (a = 0)).elim (fun h0 ↦ ⟨false, by simp [h0]⟩) fun h0 ↦ ⟨true, by simp [h a h0]⟩
    have := Fintype.card_le_of_surjective _ hsurj
    rw [← Nat.card_eq_fintype_card, hcard, Fintype.card_bool] at this
    omega
  have h3 : α ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one α hα0
    rwa [← Nat.card_eq_fintype_card, hcard] at this
  refine ⟨α, ?_⟩
  have : (α - 1) * (α ^ 2 + α + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hα1)

/-! ### The symmetric group on three letters -/

/-- The symmetric group `S₃`. -/
abbrev S₃ : Type := Equiv.Perm (Fin 3)

/-- The `3`-cycle `ρ = (0 1 2)` of `S₃`. -/
abbrev ρ : S₃ := finRotate 3

/-- The classes of `S₃`: the identity, the `3`-cycles and the transpositions. -/
def classOfS₃ (g : S₃) : Fin 3 :=
  if g = 1 then 0 else if g * g * g = 1 then 1 else 2

/-- `classOfS₃` only identifies conjugate elements. -/
theorem isConj_of_classOfS₃_eq (g h : S₃) (hgh : classOfS₃ g = classOfS₃ h) : IsConj g h := by
  revert g h
  simp only [isConj_iff, classOfS₃]
  decide +kernel

/-- `1 + ρ + ρ²` is central in `𝔽₂[S₃]`. -/
theorem one_add_of_ρ_add_of_ρ_sq_mem_center :
    1 + of (ZMod 2) S₃ ρ + of (ZMod 2) S₃ (ρ ^ 2) ∈
      Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) S₃) := by
  refine mem_center_of_coeff_conj ?_
  simp only [coeff_add, of_apply, one_def, coeff_single, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  decide +kernel

/-- `ρ + ρ²` is central in `𝔽₂[S₃]`. -/
theorem of_ρ_add_of_ρ_sq_mem_center :
    of (ZMod 2) S₃ ρ + of (ZMod 2) S₃ (ρ ^ 2) ∈
      Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) S₃) := by
  refine mem_center_of_coeff_conj ?_
  simp only [coeff_add, of_apply, coeff_single, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  decide +kernel

/-- The block idempotent `1 + ρ + ρ²` of `𝔽₂[S₃]`. -/
noncomputable def blockOneS₃ : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) S₃) :=
  ⟨_, one_add_of_ρ_add_of_ρ_sq_mem_center⟩

/-- The block idempotent `ρ + ρ²` of `𝔽₂[S₃]`. -/
noncomputable def blockTwoS₃ : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) S₃) :=
  ⟨_, of_ρ_add_of_ρ_sq_mem_center⟩

/-- The coefficient function of `1 + ρ + ρ²` is the indicator of `{g | g³ = 1}`. -/
theorem coeff_blockOneS₃ : ⇑(blockOneS₃ : MonoidAlgebra (ZMod 2) S₃).coeff =
    fun g ↦ if g * g * g = 1 then 1 else 0 := by
  funext g
  revert g
  simp only [blockOneS₃, coeff_add, of_apply, one_def, coeff_single, Finsupp.coe_add,
    Pi.add_apply, Finsupp.single_apply]
  decide +kernel

/-- The coefficient function of `ρ + ρ²` is the indicator of the `3`-cycles. -/
theorem coeff_blockTwoS₃ : ⇑(blockTwoS₃ : MonoidAlgebra (ZMod 2) S₃).coeff =
    fun g ↦ if g ≠ 1 ∧ g * g * g = 1 then 1 else 0 := by
  funext g
  revert g
  simp only [blockTwoS₃, coeff_add, of_apply, coeff_single, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply]
  decide +kernel

/-- `1 + ρ + ρ²` is a block idempotent of `𝔽₂[S₃]`. -/
theorem isBlockIdempotent_blockOneS₃ : IsBlockIdempotent blockOneS₃ :=
  isBlockIdempotent_of_coeff classOfS₃ isConj_of_classOfS₃_eq coeff_blockOneS₃
    (by decide +kernel) (by decide +kernel) (by simp only [classOfS₃]; decide +kernel)

/-- `ρ + ρ²` is a block idempotent of `𝔽₂[S₃]`. -/
theorem isBlockIdempotent_blockTwoS₃ : IsBlockIdempotent blockTwoS₃ :=
  isBlockIdempotent_of_coeff classOfS₃ isConj_of_classOfS₃_eq coeff_blockTwoS₃
    (by decide +kernel) (by decide +kernel) (by simp only [classOfS₃]; decide +kernel)

/-- The blocks of `𝔽₂[S₃]` sum to `1`. -/
theorem blockOneS₃_add_blockTwoS₃ : blockOneS₃ + blockTwoS₃ = 1 := by
  refine Subtype.ext (ext (DFunLike.coe_injective ?_))
  simp only [Subalgebra.coe_add, coeff_add, Finsupp.coe_add, coeff_blockOneS₃,
    coeff_blockTwoS₃, OneMemClass.coe_one, one_def, coeff_single]
  funext g
  revert g
  simp only [Pi.add_apply, Finsupp.single_apply]
  decide +kernel

/-- The blocks of `𝔽₂[S₃]` are orthogonal. -/
theorem blockOneS₃_mul_blockTwoS₃ : blockOneS₃ * blockTwoS₃ = 0 := by
  refine Subtype.ext (ext (Finsupp.ext fun g ↦ ?_))
  rw [Subalgebra.coe_mul, coeff_mul_eq_sum, coeff_blockOneS₃, coeff_blockTwoS₃]
  revert g
  simp only [ZeroMemClass.coe_zero, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  decide +kernel

/-- **`𝔽₃[S₃]` has a single block**: its only block idempotent is `1`. -/
theorem isBlockIdempotent_iff_eq_one_zmod_three_s₃
    (b : Subalgebra.center (ZMod 3) (MonoidAlgebra (ZMod 3) S₃)) :
    IsBlockIdempotent b ↔ b = 1 := by
  have hχ : ⇑((1 : Subalgebra.center (ZMod 3) (MonoidAlgebra (ZMod 3) S₃)) :
      MonoidAlgebra (ZMod 3) S₃).coeff = fun g ↦ if g = 1 then 1 else 0 := by
    funext g
    simp [one_def, Finsupp.single_apply, eq_comm]
  refine ⟨eq_of_isBlockIdempotent classOfS₃ isConj_of_classOfS₃_eq hχ
    (by simp only [classOfS₃]; decide +kernel), ?_⟩
  rintro rfl
  exact isBlockIdempotent_of_coeff classOfS₃ isConj_of_classOfS₃_eq hχ (by decide +kernel)
    (by decide +kernel) (by simp only [classOfS₃]; decide +kernel)

/-! ### Lifting blocks to `ℤ₂` -/

section Lift

open _root_.IsLocalRing

/-- Reduction modulo `2` detects blocks: a central idempotent of `ℤ₂[G]` is a block idempotent
exactly when its reduction in `𝔽₂[G]` is. -/
theorem isBlockIdempotent_centerMapRingHom_toZMod_iff {G : Type*} [Group G] [Finite G]
    {b : Subalgebra.center ℤ_[2] (MonoidAlgebra ℤ_[2] G)} (hb : IsIdempotentElem b) :
    IsBlockIdempotent (centerMapRingHom G PadicInt.toZMod b) ↔ IsBlockIdempotent b :=
  isBlockIdempotent_centerMapRingHom_iff (maximalIdeal ℤ_[2]) (ZMod.ringHom_surjective _)
    PadicInt.ker_toZMod hb

/-- Two block idempotents of `ℤ₂[G]` with the same reduction in `𝔽₂[G]` are equal. -/
theorem eq_of_centerMapRingHom_toZMod_eq {G : Type*} [Group G] [Finite G]
    {b c : Subalgebra.center ℤ_[2] (MonoidAlgebra ℤ_[2] G)} (hb : IsBlockIdempotent b)
    (hc : IsBlockIdempotent c)
    (h : centerMapRingHom G PadicInt.toZMod b = centerMapRingHom G PadicInt.toZMod c) :
    b = c :=
  (bijOn_centerMapRingHom_isBlockIdempotent (maximalIdeal ℤ_[2]) (ZMod.ringHom_surjective _)
    PadicInt.ker_toZMod).injOn hb hc h

/-- The maximal ideal `(2)` of `ℤ₂` is not nilpotent. -/
theorem not_isNilpotent_maximalIdeal : ¬ IsNilpotent (maximalIdeal ℤ_[2]) := by
  rintro ⟨n, hn⟩
  have h2 : (2 : ℤ_[2]) ∈ maximalIdeal ℤ_[2] := by
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat]
    decide
  have : (2 : ℤ_[2]) ^ n ∈ maximalIdeal ℤ_[2] ^ n := Ideal.pow_mem_pow h2 n
  rw [hn, Submodule.zero_eq_bot, Ideal.mem_bot] at this
  exact pow_ne_zero n two_ne_zero this

/-- **Blocks of `ℤ₂[1]`.** The only block idempotent of `ℤ₂[1]` is `1`, the lift of the block `1`
of `𝔽₂[1]`, although the maximal ideal of `ℤ₂` is not nilpotent
(`not_isNilpotent_maximalIdeal`). -/
theorem isBlockIdempotent_iff_eq_one_padicInt_unit
    (b : Subalgebra.center ℤ_[2] (MonoidAlgebra ℤ_[2] Unit)) : IsBlockIdempotent b ↔ b = 1 := by
  have hχ : ⇑((1 : Subalgebra.center (ZMod 2) (MonoidAlgebra (ZMod 2) Unit)) :
      MonoidAlgebra (ZMod 2) Unit).coeff = fun _ ↦ 1 := by
    funext g
    simp [one_def]
  have h1 : IsBlockIdempotent (1 : Subalgebra.center ℤ_[2] (MonoidAlgebra ℤ_[2] Unit)) := by
    rw [← isBlockIdempotent_centerMapRingHom_toZMod_iff .one, map_one]
    exact isBlockIdempotent_of_coeff id isConj_of_id_eq hχ (by decide) (by decide) (by decide)
  refine ⟨fun hb ↦ eq_of_centerMapRingHom_toZMod_eq hb h1 ?_, fun h ↦ h ▸ h1⟩
  rw [map_one]
  exact eq_of_isBlockIdempotent id isConj_of_id_eq hχ (by decide)
    ((isBlockIdempotent_centerMapRingHom_toZMod_iff hb.isIdempotentElem).mpr hb)

/-- `3` is a unit of `ℤ₂`. -/
theorem exists_three_mul_eq_one : ∃ u : ℤ_[2], 3 * u = 1 := by
  have : IsUnit (3 : ℤ_[2]) := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat]
    decide
  obtain ⟨u, hu⟩ := this.exists_right_inv
  exact ⟨u, hu⟩

variable {u : ℤ_[2]}

/-- The inverse of `3` in `ℤ₂` reduces to `1` modulo `2`. -/
theorem toZMod_eq_one (hu : 3 * u = 1) : PadicInt.toZMod u = 1 := by
  have := congr_arg PadicInt.toZMod hu
  rw [map_mul, map_one, map_ofNat] at this
  revert this
  generalize PadicInt.toZMod u = a
  revert a
  decide

/-- The coefficients of `(1 + r + r²)/3` in `ℤ₂[C₃]`. -/
theorem coeff_smul_one_add_r_add_r_sq :
    ⇑(u • (1 + of ℤ_[2] C₃ r + of ℤ_[2] C₃ (r ^ 2))).coeff = fun _ ↦ u := by
  funext g
  fin_cases g <;> simp +decide [one_def, Finsupp.single_apply]

/-- `(1 + r + r²)/3` is idempotent in `ℤ₂[C₃]`. -/
theorem isIdempotentElem_smul_one_add_r_add_r_sq (hu : 3 * u = 1) :
    IsIdempotentElem (u • (1 + of ℤ_[2] C₃ r + of ℤ_[2] C₃ (r ^ 2))) := by
  refine ext (DFunLike.coe_injective (funext fun g ↦ ?_))
  rw [coeff_mul_eq_sum, coeff_smul_one_add_r_add_r_sq, sum_c₃]
  linear_combination u * hu

/-- `(2 - r - r²)/3 = 1 - (1 + r + r²)/3` in `ℤ₂[C₃]`. -/
theorem smul_two_sub_r_sub_r_sq (hu : 3 * u = 1) :
    u • (2 - of ℤ_[2] C₃ r - of ℤ_[2] C₃ (r ^ 2)) =
      1 - u • (1 + of ℤ_[2] C₃ r + of ℤ_[2] C₃ (r ^ 2)) := by
  refine ext (Finsupp.ext fun g ↦ ?_)
  fin_cases g
  · simp +decide [one_def, Finsupp.single_apply]
    linear_combination hu
  all_goals simp +decide [one_def, Finsupp.single_apply]

/-- **Lifting the blocks of `𝔽₂[C₃]`.** The block `1 + r + r²` of `𝔽₂[C₃]` is the reduction of
`(1 + r + r²)/3`, a block idempotent of `ℤ₂[C₃]` (here `u = 1/3`). -/
theorem isBlockIdempotent_smul_one_add_r_add_r_sq (hu : 3 * u = 1) :
    IsBlockIdempotent (toCenter (u • (1 + of ℤ_[2] C₃ r + of ℤ_[2] C₃ (r ^ 2)))) ∧
      centerMapRingHom C₃ PadicInt.toZMod
          (toCenter (u • (1 + of ℤ_[2] C₃ r + of ℤ_[2] C₃ (r ^ 2)))) =
        toCenter (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) := by
  have hred : centerMapRingHom C₃ PadicInt.toZMod
      (toCenter (u • (1 + of ℤ_[2] C₃ r + of ℤ_[2] C₃ (r ^ 2)))) =
        toCenter (1 + of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) := by
    refine Subtype.ext (ext (Finsupp.ext fun g ↦ ?_))
    rw [coe_centerMapRingHom, coe_toCenter, coeff_mapRingHom, coeff_smul_one_add_r_add_r_sq,
      toZMod_eq_one hu]
    fin_cases g <;> simp +decide [one_def, Finsupp.single_apply]
  refine ⟨?_, hred⟩
  rw [← isBlockIdempotent_centerMapRingHom_toZMod_iff
    (isIdempotentElem_toCenter (isIdempotentElem_smul_one_add_r_add_r_sq hu)), hred]
  exact isBlockIdempotent_one_add_r_add_r_sq

/-- **Lifting the blocks of `𝔽₂[C₃]`.** The block `r + r²` of `𝔽₂[C₃]` is the reduction of
`(2 - r - r²)/3`, a block idempotent of `ℤ₂[C₃]` (here `u = 1/3`). -/
theorem isBlockIdempotent_smul_two_sub_r_sub_r_sq (hu : 3 * u = 1) :
    IsBlockIdempotent (toCenter (u • (2 - of ℤ_[2] C₃ r - of ℤ_[2] C₃ (r ^ 2)))) ∧
      centerMapRingHom C₃ PadicInt.toZMod
          (toCenter (u • (2 - of ℤ_[2] C₃ r - of ℤ_[2] C₃ (r ^ 2)))) =
        toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) := by
  have hred : centerMapRingHom C₃ PadicInt.toZMod
      (toCenter (u • (2 - of ℤ_[2] C₃ r - of ℤ_[2] C₃ (r ^ 2)))) =
        toCenter (of (ZMod 2) C₃ r + of (ZMod 2) C₃ (r ^ 2)) := by
    refine Subtype.ext (ext (Finsupp.ext fun g ↦ ?_))
    rw [coe_centerMapRingHom, coe_toCenter, smul_two_sub_r_sub_r_sq hu, map_sub, map_one,
      coeff_sub, Finsupp.sub_apply, coeff_mapRingHom, coeff_smul_one_add_r_add_r_sq,
      toZMod_eq_one hu]
    fin_cases g <;> simp +decide [one_def, Finsupp.single_apply]
  refine ⟨?_, hred⟩
  rw [← isBlockIdempotent_centerMapRingHom_toZMod_iff
    (isIdempotentElem_toCenter (by
      rw [smul_two_sub_r_sub_r_sq hu]
      exact (isIdempotentElem_smul_one_add_r_add_r_sq hu).one_sub)), hred]
  exact isBlockIdempotent_r_add_r_sq

/-- The ordinary idempotents `(1 ± t)/2` of `ℚ₂[C₂]` are not in `ℤ₂[C₂]`: no `x ∈ ℤ₂[C₂]`
satisfies `2 x = 1 + t` or `2 x = 1 - t`, since the coefficient of `1` would be `1/2`. -/
theorem two_smul_ne_one_add_of_t_and_one_sub_of_t (x : MonoidAlgebra ℤ_[2] C₂) :
    (2 : ℤ_[2]) • x ≠ 1 + of ℤ_[2] C₂ t ∧ (2 : ℤ_[2]) • x ≠ 1 - of ℤ_[2] C₂ t := by
  have key (y : MonoidAlgebra ℤ_[2] C₂) (hy : y.coeff 1 = 1) : (2 : ℤ_[2]) • x ≠ y := by
    intro h
    have := congr_arg (fun z : MonoidAlgebra ℤ_[2] C₂ ↦ PadicInt.toZMod (z.coeff 1)) h
    simp only [coeff_smul_apply, smul_eq_mul, map_mul, map_ofNat, hy, map_one] at this
    revert this
    generalize PadicInt.toZMod (x.coeff 1) = a
    revert a
    decide
  exact ⟨key _ (by simp +decide [one_def]), key _ (by simp +decide [one_def])⟩

/-- **Blocks of `ℤ₂[C₂]`.** The only block idempotent of `ℤ₂[C₂]` is `1`, matching the single block
of `𝔽₂[C₂]`. -/
theorem isBlockIdempotent_iff_eq_one_padicInt_c₂
    (b : Subalgebra.center ℤ_[2] (MonoidAlgebra ℤ_[2] C₂)) : IsBlockIdempotent b ↔ b = 1 := by
  have h1 : IsBlockIdempotent (1 : Subalgebra.center ℤ_[2] (MonoidAlgebra ℤ_[2] C₂)) := by
    rw [← isBlockIdempotent_centerMapRingHom_toZMod_iff .one, map_one,
      isBlockIdempotent_iff_eq_one_zmod_two_c₂]
  refine ⟨fun hb ↦ eq_of_centerMapRingHom_toZMod_eq hb h1 ?_, fun h ↦ h ▸ h1⟩
  rw [map_one, ← isBlockIdempotent_iff_eq_one_zmod_two_c₂]
  exact (isBlockIdempotent_centerMapRingHom_toZMod_iff hb.isIdempotentElem).mpr hb

end Lift

end TauCeti.GroupAlgebraBlockExamples
