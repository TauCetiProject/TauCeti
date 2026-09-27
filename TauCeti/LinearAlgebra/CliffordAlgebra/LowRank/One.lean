/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import TauCeti.Algebra.GroupWithZero.Units.Basic

/-!
# Even Clifford elements in dimension one

Every even element of a rank-one Clifford algebra is the image of a scalar, over any field,
including one of characteristic two. The corresponding statement for units follows from the
unit-lifting lemma for a homomorphism out of a group with zero.

The scalar calculation follows the standard Clifford algebra argument; see H. B. Lawson and
M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.

## Main results

* `CliffordAlgebra.exists_eq_algebraMap_of_mem_even_of_finrank_eq_one`: every even element is a
  scalar in dimension one.
* `CliffordAlgebra.exists_eq_unitsMap_algebraMap_of_mem_even_of_finrank_eq_one`: every even unit
  comes from a unit of the base field.
-/

public section

namespace CliffordAlgebra

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  (Q : QuadraticForm K V)

/-- In dimension one, every even Clifford element equals the image of a scalar, over any field. -/
theorem exists_eq_algebraMap_of_mem_even_of_finrank_eq_one
    (hV : Module.finrank K V = 1) (y : CliffordAlgebra Q) (hy : y ∈ even Q) :
    ∃ a : K, y = algebraMap K (CliffordAlgebra Q) a := by
  let _ : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; decide)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hpair (m₁ m₂ : V) :
      ∃ a : K, ι Q m₁ * ι Q m₂ = algebraMap K (CliffordAlgebra Q) a := by
    obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one hV hv m₁
    obtain ⟨b, rfl⟩ := exists_smul_eq_of_finrank_eq_one hV hv m₂
    refine ⟨a * b * Q v, ?_⟩
    rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def]
    calc
      _ = (algebraMap K (CliffordAlgebra Q)) a *
          ((algebraMap K (CliffordAlgebra Q)) b * (ι Q v * ι Q v)) := by
        rw [mul_assoc (algebraMap K (CliffordAlgebra Q) a),
          ← mul_assoc (ι Q v) (algebraMap K (CliffordAlgebra Q) b) (ι Q v),
          ← Algebra.commutes b (ι Q v)]
        simp only [mul_assoc]
      _ = _ := by rw [ι_sq_scalar, ← map_mul, ← map_mul, mul_assoc]
  induction y, hy using even_induction with
  | algebraMap a => exact ⟨a, rfl⟩
  | add y z _ _ ihy ihz =>
    obtain ⟨a, ha⟩ := ihy
    obtain ⟨b, hb⟩ := ihz
    exact ⟨a + b, by rw [ha, hb, map_add]⟩
  | ι_mul_ι_mul m₁ m₂ y _ ih =>
    obtain ⟨a, ha⟩ := hpair m₁ m₂
    obtain ⟨b, hb⟩ := ih
    exact ⟨a * b, by rw [ha, hb, map_mul]⟩

/-- In dimension one, every even Clifford unit equals the image of a unit of the base field. -/
theorem exists_eq_unitsMap_algebraMap_of_mem_even_of_finrank_eq_one
    (hV : Module.finrank K V = 1) (x : (CliffordAlgebra Q)ˣ)
    (hx : (x : CliffordAlgebra Q) ∈ even Q) :
    ∃ a : Kˣ, x = Units.map (algebraMap K (CliffordAlgebra Q)) a := by
  obtain ⟨a, ha⟩ := exists_eq_algebraMap_of_mem_even_of_finrank_eq_one Q hV x hx
  rcases subsingleton_or_nontrivial (CliffordAlgebra Q) with htriv | hnontriv
  · have : Subsingleton (CliffordAlgebra Q) := htriv
    exact ⟨1, Subsingleton.elim _ _⟩
  have : Nontrivial (CliffordAlgebra Q) := hnontriv
  obtain ⟨b, hb⟩ :=
    (TauCeti.mem_range_iff_exists_units_map_eq
      (algebraMap K (CliffordAlgebra Q)) x).mp ⟨a, ha.symm⟩
  exact ⟨b, hb.symm⟩

end CliffordAlgebra
