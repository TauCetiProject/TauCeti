/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.Algebra.MonoidAlgebra.Eigenvector
public import TauCeti.RepresentationTheory.CharacterTable.ClassSum.Basis
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Basic

/-!
# Criteria for block idempotents

Criteria for an element of the centre of a group algebra `k[G]` of a finite group to be a block
idempotent (`TauCeti.IsBlockIdempotent`), suited to explicit computations.

The coefficients of a central element are constant on conjugacy classes
(`TauCeti.center_coeff_eq_of_isConj`), so for any map `cls : G → ι` identifying only conjugate
elements they factor through `cls` (`TauCeti.exists_center_coeff_eq_comp`). Multiplication in
`k[G]` is convolution of coefficient functions (`MonoidAlgebra.coeff_mul_eq_sum`), so the
idempotents of the centre absorbed by a central element `b` are the idempotent functions `ψ ∘ cls`
absorbed by the coefficient function of `b`. When `G`, `ι` and `k` are finite these conditions are
decidable, which gives a criterion for `b` to be a block idempotent
(`TauCeti.isBlockIdempotent_of_coeff`) and one for `b` to be the only block idempotent
(`TauCeti.eq_of_isBlockIdempotent_of_coeff`).

A central element `b` on which every `g ∈ G` acts by a scalar `c(g)` spans its block algebra
`b k[G] = k b` (`TauCeti.mul_eq_smul_of_mul_of_eq_smul`). Over a domain it is a block idempotent
when its coefficient at `1` is `1` and `∑ g, b(g) c(g) = 1`
(`TauCeti.isBlockIdempotent_of_mul_of_eq_smul`).

## Main results

* `TauCeti.isBlockIdempotent_of_coeff`: a block criterion on coefficient functions.
* `TauCeti.eq_of_isBlockIdempotent_of_coeff`: a uniqueness criterion on coefficient functions.
* `TauCeti.isBlockIdempotent_of_mul_of_eq_smul`: blocks whose block algebra is the line `k b`.
-/

public section

open MonoidAlgebra

namespace TauCeti

variable {k G : Type*} [CommSemiring k] [Group G] [Fintype G]

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
    rw [ZeroMemClass.coe_zero, coeff_zero, Finsupp.coe_zero] at hb
    exact hne hb.symm
  · obtain ⟨ψ, hψ⟩ := exists_center_coeff_eq_comp cls hcls f
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
theorem eq_of_isBlockIdempotent_of_coeff {ι : Type*} (cls : G → ι)
    (hcls : ∀ g h, cls g = cls h → IsConj g h)
    {c : Subalgebra.center k (MonoidAlgebra k G)} {χ : G → k}
    (hc : ⇑(c : MonoidAlgebra k G).coeff = χ)
    (h : ∀ ψ : ι → k, (∀ g, ∑ h, ψ (cls h) * ψ (cls (h⁻¹ * g)) = ψ (cls g)) →
      ψ ∘ cls ≠ 0 → ψ ∘ cls = χ)
    {b : Subalgebra.center k (MonoidAlgebra k G)} (hb : IsBlockIdempotent b) : b = c := by
  obtain ⟨ψ, hψ⟩ := exists_center_coeff_eq_comp cls hcls b
  have hidem (g : G) : ∑ h, ψ (cls h) * ψ (cls (h⁻¹ * g)) = ψ (cls g) := by
    have := hb.isIdempotentElem_val
    rw [IsIdempotentElem, ← coeff_inj] at this
    have := DFunLike.congr_fun this g
    simpa only [coeff_mul_eq_sum, hψ, Function.comp_apply] using this
  have hne : ψ ∘ cls ≠ 0 := fun h0 ↦ hb.ne_zero <| Subtype.ext <| ext <|
    DFunLike.coe_injective (hψ.trans h0)
  exact Subtype.ext (ext (DFunLike.coe_injective (hψ.trans ((h ψ hidem hne).trans hc.symm))))

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
    · exact .inl (Subtype.ext (by rw [hfs, h0, zero_smul, ZeroMemClass.coe_zero]))
    · exact .inr (Subtype.ext (by rw [hfs, h1, one_smul]))

end TauCeti
