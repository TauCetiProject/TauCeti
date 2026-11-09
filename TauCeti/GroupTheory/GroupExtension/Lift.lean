/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.FactorSetOfSection

/-!
# Homomorphisms out of a group extension

A homomorphism out of an extension is determined by its values on the kernel and on a
normalized section. The two compatibility conditions are conjugation of the kernel and
the section's factor-set multiplication law. This universal property also applies to
monoid targets, such as the endomorphisms of a module, without first constructing inverses.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace GroupExtension.Section

open TauCeti.GroupExtension

variable {K E Q H : Type*} [Group K] [Group E] [Group Q] [Monoid H]
  {S : GroupExtension K E Q} (s : S.Section) (hs : s 1 = 1)
  (f : K →* H) (u : Q → H) (hu : u 1 = 1)
  (hconj : ∀ q d, u q * f d = f (S.conjAct (s q) d) * u q)
  (hmul : ∀ q r, u q * u r = f (factorSetFun s (q, r)) * u (q * r))

/-- Every element factors as a kernel element followed by its section representative. -/
theorem exists_eq_inl_mul_section (e : E) :
    ∃ d : K, e = S.inl d * s (S.rightHom e) := by
  have he : e * (s (S.rightHom e))⁻¹ ∈ S.inl.range := by
    simp [S.range_inl_eq_ker_rightHom]
  obtain ⟨d, hd⟩ := he
  exact ⟨d, by rw [hd, inv_mul_cancel_right]⟩

/-- Extend compatible kernel and section maps to a homomorphism on the whole extension. -/
noncomputable def lift : E →* H := by
  classical
  choose d hd using exists_eq_inl_mul_section s
  have hcoord (a : K) (q : Q) : d (S.inl a * s q) = a := by
    apply S.inl_injective
    have h := hd (S.inl a * s q)
    simpa only [map_mul, S.rightHom_inl, rightHom_section, one_mul,
      mul_left_inj] using h.symm
  refine
    { toFun := fun e => f (d e) * u (S.rightHom e)
      map_one' := ?_
      map_mul' := ?_ }
  · have hd1 : d 1 = 1 := by
      apply S.inl_injective
      simpa [hs] using (hd 1).symm
    simp [hd1, hu]
  · intro e e'
    obtain ⟨a, ha⟩ := exists_eq_inl_mul_section s e
    obtain ⟨b, hb⟩ := exists_eq_inl_mul_section s e'
    let q := S.rightHom e
    let r := S.rightHom e'
    have he : e * e' = S.inl (a * S.conjAct (s q) b * factorSetFun s (q, r)) * s (q * r) := by
      rw [ha, hb]
      simp only [q, r, map_mul, S.inl_conjAct_comm, inl_factorSetFun]
      group
    rw [he, hcoord]
    simp only [map_mul, S.rightHom_inl, rightHom_section, one_mul]
    rw [ha, hb, hcoord, hcoord]
    simp only [map_mul, S.rightHom_inl, rightHom_section, one_mul]
    calc
      _ = f a * ((f (S.conjAct (s q) b) * u q) * u r) := by
        simp only [mul_assoc]
        rw [← hmul]
      _ = _ := by rw [← hconj]; simp [q, r, mul_assoc]

private theorem lift_inl_mul (d : K) (q : Q) :
    lift s hs f u hu hconj hmul (S.inl d * s q) = f d * u q := by
  classical
  simp only [lift, MonoidHom.coe_mk, OneHom.coe_mk]
  congr 1
  · congr 1
    apply S.inl_injective
    have h := (exists_eq_inl_mul_section s (S.inl d * s q)).choose_spec
    simpa only [map_mul, S.rightHom_inl, rightHom_section, one_mul, mul_left_inj] using h.symm
  · simp

/-- The lift restricts to the given kernel homomorphism. -/
@[simp]
theorem lift_inl (d : K) : lift s hs f u hu hconj hmul (S.inl d) = f d := by
  simpa [hs, hu] using lift_inl_mul s hs f u hu hconj hmul d 1

/-- The lift takes the prescribed values on the section. -/
@[simp]
theorem lift_section (q : Q) : lift s hs f u hu hconj hmul (s q) = u q := by
  simpa using lift_inl_mul s hs f u hu hconj hmul 1 q

/-- Kernel and section values determine a homomorphism out of the extension. -/
theorem hom_ext {F F' : E →* H} (hf : ∀ d, F (S.inl d) = F' (S.inl d))
    (hu : ∀ q, F (s q) = F' (s q)) : F = F' := by
  ext e
  obtain ⟨d, hd⟩ := exists_eq_inl_mul_section s e
  rw [hd, map_mul, map_mul, hf, hu]

end GroupExtension.Section
