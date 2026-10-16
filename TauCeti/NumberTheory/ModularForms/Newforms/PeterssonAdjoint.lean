/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
public import TauCeti.NumberTheory.ModularForms.Petersson.Normal
public import TauCeti.NumberTheory.ModularForms.Petersson.Unitary
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The Petersson adjoint on good Hecke eigenforms

On `S_k(N, χ)` the Petersson adjoint of the Hecke operator `Tₚ` at a prime `p ∤ N` is
`χ(p)⁻¹ Tₚ`. Evaluated on good Hecke eigenforms this gives two consequences for their
eigenvalues.

*Reality up to the nebentypus.* A good Hecke eigenform pairs nontrivially with itself, so its
eigenvalue `λ_p` is fixed by `c ↦ conj (χ(p)⁻¹ c)`, that is `λ_p = χ(p) · conj λ_p`.

*Orthogonality.* Good Hecke eigenforms whose eigenvalues differ at a prime `p ∤ N` are
orthogonal: for a common nebentypus `χ` because of the adjoint relation, and otherwise because
the nebentypus decomposition is orthogonal.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.eigenvalue_eq_mul_conj`: at a good prime `p`, the
  eigenvalue of a good Hecke eigenform satisfies `λ_p = χ(p) · conj λ_p`.
* `HeckeRing.GL2.EigenformAwayFromLevel.peterssonInnerCosets_eq_zero_of_eigenvalue_ne`: good
  Hecke eigenforms with distinct eigenvalues at a good prime are orthogonal.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13(2).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti ComplexConjugate

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

namespace EigenformAwayFromLevel

/-- A good Hecke eigenform of nebentypus `χ`, seen in `S_k(N, χ)`, is an eigenvector of the Hecke
ring generator `Tₚ` at every prime `p` not dividing `N`, with its eigenvalue at `p`. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul
    {f : EigenformAwayFromLevel N k} {x : cuspFormCharSpace k χ} (hχ : f.χ = χ)
    (hx : f.toCuspForm = (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) {p : ℕ} (hp : p.Prime)
    (hpN : Nat.Coprime p N) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) x =
      f.eigenvalue ⟨p, hp.pos⟩ hpN • x := by
  obtain ⟨F, χ', hF, a, haF, _⟩ := f
  obtain rfl : χ' = χ := hχ
  obtain rfl : ⟨F, hF⟩ = x := Subtype.ext hx
  simpa only [PNat.mk_coe, heckeTCompositeGamma0_prime N hp] using haF ⟨p, hp.pos⟩ hpN

/-- The Petersson adjoint `χ(p)⁻¹ Tₚ` of `Tₚ` on `S_k(N, χ)`, evaluated on two eigenvectors. -/
private theorem sub_mul_peterssonInnerCosets_eq_zero {p : ℕ} (hp : p.Prime)
    (hpN : Nat.Coprime p N) (x y : cuspFormCharSpace k χ) (α β : ℂ)
    (hx : heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) x = α • x)
    (hy : heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) y = β • y) :
    (α - conj ((χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹ * β)) *
      CuspForm.peterssonInnerCosets (y : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) x = 0 := by
  have hadj := isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 (χ := χ) k hp
    hpN x y
  simp only [LinearMap.flip_apply,
    TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ_apply_apply, Pi.smul_apply, hx, hy,
    Submodule.coe_smul, CuspForm.peterssonInnerCosets_smul_left,
    CuspForm.peterssonInnerCosets_smul_right] at hadj
  rw [map_mul]
  linear_combination hadj

/-- A good Hecke eigenform pairs nontrivially with itself, so its eigenvalue at a good prime is
fixed by the antilinear map `c ↦ conj (χ(p)⁻¹ c)` coming from the adjoint of `Tₚ`. -/
private theorem conj_inv_mul_eigenvalue (f : EigenformAwayFromLevel N k) {p : ℕ}
    (hp : p.Prime) (hpN : Nat.Coprime p N) :
    conj ((f.χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹ * f.eigenvalue ⟨p, hp.pos⟩ hpN) =
      f.eigenvalue ⟨p, hp.pos⟩ hpN := by
  let y : cuspFormCharSpace k f.χ := ⟨f.toCuspForm, f.mem_charSpace⟩
  have hy := heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul (x := y) rfl rfl hp hpN
  exact (sub_eq_zero.mp ((mul_eq_zero.mp (sub_mul_peterssonInnerCosets_eq_zero hp hpN y y _ _
    hy hy)).resolve_right (mt (CuspForm.peterssonInnerCosets_self_eq_zero _).mp f.ne_zero))).symm

/-- **The eigenvalues of a good Hecke eigenform are real up to the nebentypus**: at a prime
`p ∤ N`, the eigenvalue `λ_p` of a good Hecke eigenform of nebentypus `χ` satisfies
`λ_p = χ(p) · conj λ_p`. This is the shadow of the Petersson adjoint `Tₚ* = χ(p)⁻¹ Tₚ` on the
eigenvector; for `χ(p) = 1`, for instance for trivial nebentypus, it says that `λ_p` is real. -/
theorem eigenvalue_eq_mul_conj (f : EigenformAwayFromLevel N k) {p : ℕ} (hp : p.Prime)
    (hpN : Nat.Coprime p N) :
    f.eigenvalue ⟨p, hp.pos⟩ hpN =
      f.χ (ZMod.unitOfCoprime p hpN) * conj (f.eigenvalue ⟨p, hp.pos⟩ hpN) := by
  set u : ℂ := (f.χ (ZMod.unitOfCoprime p hpN) : ℂ)
  -- the character value lies on the unit circle, so `conj u⁻¹ = u`
  have hu : conj u⁻¹ = u := by
    have h := DirichletCharacter.unit_norm_eq_one (MulChar.ofUnitHom f.χ)
      (ZMod.unitOfCoprime p hpN)
    rw [MulChar.ofUnitHom_coe] at h
    rw [map_inv₀, ← Complex.inv_eq_conj h, inv_inv]
  conv_lhs => rw [← conj_inv_mul_eigenvalue f hp hpN, map_mul, hu]

/-- **Good Hecke eigenforms with distinct eigenvalues are orthogonal.** Two good Hecke
eigenforms whose eigenvalues differ at a prime `p` not dividing `N` are Petersson-orthogonal. -/
theorem peterssonInnerCosets_eq_zero_of_eigenvalue_ne {f g : EigenformAwayFromLevel N k}
    {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N)
    (hne : f.eigenvalue ⟨p, hp.pos⟩ hpN ≠ g.eigenvalue ⟨p, hp.pos⟩ hpN) :
    CuspForm.peterssonInnerCosets f.toCuspForm g.toCuspForm = 0 := by
  -- forms of distinct nebentypus are orthogonal
  obtain hχ | hχ := ne_or_eq f.χ g.χ
  · exact CuspForm.peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne hχ
      f.mem_charSpace g.mem_charSpace
  let x : cuspFormCharSpace k g.χ := ⟨f.toCuspForm, hχ ▸ f.mem_charSpace⟩
  let y : cuspFormCharSpace k g.χ := ⟨g.toCuspForm, g.mem_charSpace⟩
  have hx := heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul (x := x) hχ rfl hp hpN
  have hy := heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul (x := y) rfl rfl hp hpN
  have hyx := sub_mul_peterssonInnerCosets_eq_zero hp hpN x y _ _ hx hy
  rw [conj_inv_mul_eigenvalue g hp hpN] at hyx
  rw [← CuspForm.peterssonInnerCosets_conj_symm, (mul_eq_zero.mp hyx).resolve_left
    (sub_ne_zero.mpr hne), map_zero]

end EigenformAwayFromLevel

end HeckeRing.GL2
