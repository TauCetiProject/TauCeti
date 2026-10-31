/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.Basic
public import TauCeti.LinearAlgebra.Matrix.OrderedSignCover.SectionSign
public import Mathlib.LinearAlgebra.Basis.SMul

/-!
# The action of compatible sign-cover lifts on the signed shell Lie algebra

Let `B : Matrix I I ℤ` and `B' : Matrix J J ℤ` be Gram matrices on linearly ordered finite sets,
and let `g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)` be an isometry of their Gram lattices,
`⟪g a, g b⟫' = ⟪a, b⟫`. It restricts to a bijection `a ↦ g a` of norm-two shells
(`Matrix.normTwoShellEquivOfIsometry`). The bracket of `Matrix.ShellLieAlgebra B` on root vectors
involves the ordered sign `ε` of `B`, and `g` need not carry `ε` to the ordered sign `ε'` of `B'`,
so `x_a ↦ x_(g a)` is not a Lie map in general. A homomorphism `φ` of ordered sign covers that
fixes the kernel `ℤˣ` and lies over `g` supplies the correcting signs: its section signs
`s_φ(a)`, defined by `φ (1, a) = s_φ(a) (1, g a)` (`Matrix.SignCover.sectionSign`), satisfy
`ε(a, b) s_φ(a + b) = ε'(g a, g b) s_φ(a) s_φ(b)`.

This file constructs the linear equivalence `Matrix.ShellLieAlgebra.coverEquiv φ g`,

`H_h ↦ H_(g h)`,  `x_a ↦ s_φ(a) x_(g a)`,

from `ShellLieAlgebra B` to `ShellLieAlgebra B'`, and shows that for such a compatible pair
`(φ, g)` it preserves the bracket (`Matrix.ShellLieAlgebra.coverEquiv_lie`). When `B` and `B'`
are positive definite with even diagonal, so that the signed Lie rings are defined, it is therefore
an isomorphism of them (`Matrix.ShellLieAlgebra.coverLieEquiv`). No symmetry or definiteness of `B`
is needed for the bracket identity, since the sign identity is supplied by `φ`.
The action is functorial: the identity pair acts by the identity, and a composite pair acts by the
composite (`Matrix.ShellLieAlgebra.coverEquiv_id`, `Matrix.ShellLieAlgebra.coverEquiv_trans`). It
is faithful when the norm-two shell spans the lattice: the Cartan vectors detect `g`, the root
vectors detect the section signs of `φ` on the shell, and over the identity these signs form a
character of the lattice that determines `φ` (`Matrix.ShellLieAlgebra.coverEquiv_eq_refl_iff`).

## Main definitions

* `Matrix.ShellLieAlgebra.coverEquiv φ g hg`: the linear equivalence `H_h ↦ H_(g h)`,
  `x_a ↦ s_φ(a) x_(g a)`.
* `Matrix.ShellLieAlgebra.coverLieEquiv`: the same map as an isomorphism of Lie algebras over `ℤ`,
  for positive definite Gram matrices with even diagonal.

## Main results

* `Matrix.ShellLieAlgebra.coverEquiv_cartan`, `Matrix.ShellLieAlgebra.coverEquiv_root`: the values
  on Cartan and root vectors.
* `Matrix.ShellLieAlgebra.coverEquiv_symm_cartan`, `Matrix.ShellLieAlgebra.coverEquiv_symm_root`:
  the values of the inverse on Cartan and root vectors.
* `Matrix.ShellLieAlgebra.coverEquiv_rootBracket`: the image of a root bracket.
* `Matrix.ShellLieAlgebra.coverEquiv_lie`: a compatible pair preserves the bracket.
* `Matrix.ShellLieAlgebra.coverEquiv_id`, `Matrix.ShellLieAlgebra.coverEquiv_trans`:
  functoriality.
* `Matrix.ShellLieAlgebra.coverEquiv_eq_refl_iff`: the action is faithful when the norm-two shell
  spans the lattice.

## References

* I. B. Frenkel, J. Lepowsky and A. Meurman, *Vertex operator algebras and the Monster*, Academic
  Press (1988), §§5.4 and 6.4, for automorphisms of the central extension of a lattice lying over
  lattice isometries and their action on the associated Lie algebra.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix.ShellLieAlgebra

open TauCeti Module

attribute [local instance] trivialMulDistribMulAction

variable {I J K : Type*} [Fintype I] [LinearOrder I] [Fintype J] [LinearOrder J] [Fintype K]
  [LinearOrder K] {B : Matrix I I ℤ} {B' : Matrix J J ℤ} {B'' : Matrix K K ℤ}
  (φ : SignCover B →* SignCover B') (g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
  (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b)

/-- **The action of a sign-cover lift on the signed shell Lie algebra.** For an isometry
`g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)` of the Gram lattices of `B` and `B'` and a homomorphism
`φ : SignCover B →* SignCover B'` of ordered sign covers, the linear equivalence
`ShellLieAlgebra B ≃ₗ[ℤ] ShellLieAlgebra B'` sending the Cartan vector `H_h` to `H_(g h)` and the
root vector `x_a` to `s_φ(a) x_(g a)`, where `s_φ` is the section sign
`Matrix.SignCover.sectionSign φ`. It preserves the bracket when `φ` fixes the kernel `ℤˣ` and lies
over `g` (`Matrix.ShellLieAlgebra.coverEquiv_lie`). -/
noncomputable def coverEquiv : ShellLieAlgebra B ≃ₗ[ℤ] ShellLieAlgebra B' :=
  equivProd B ≪≫ₗ
    g.prodCongr (Finsupp.basisSingleOne.equiv (Finsupp.basisSingleOne.unitsSMul fun b =>
        SignCover.sectionSign φ ((normTwoShellEquivOfIsometry g hg).symm b))
      (normTwoShellEquivOfIsometry g hg)) ≪≫ₗ
    (equivProd B').symm

/-- The action of a sign-cover lift sends the Cartan vector `H_h` to `H_(g h)`. -/
@[simp]
theorem coverEquiv_cartan (h : I → ℤ) : coverEquiv φ g hg (cartan B h) = cartan B' (g h) := by
  apply (equivProd B').injective
  simp [coverEquiv]

/-- The action of a sign-cover lift sends the root vector `x_a` to `s_φ(a) x_(g a)`. -/
@[simp]
theorem coverEquiv_root (a : B.normTwoShell) :
    coverEquiv φ g hg (root B a) =
      SignCover.sectionSign φ a • root B' (normTwoShellEquivOfIsometry g hg a) := by
  apply (equivProd B').injective
  simp only [coverEquiv, LinearEquiv.trans_apply, equivProd_root, LinearEquiv.prodCongr_apply,
    map_zero, LinearEquiv.apply_symm_apply, map_zsmul_unit, Prod.smul_mk, smul_zero]
  rw [← congrFun Finsupp.coe_basisSingleOne a, Basis.equiv_apply, Basis.unitsSMul_apply,
    Equiv.symm_apply_apply, Finsupp.coe_basisSingleOne]

/-- The inverse of the action of a sign-cover lift sends the Cartan vector `H_h` to
`H_(g⁻¹ h)`. -/
@[simp]
theorem coverEquiv_symm_cartan (h : J → ℤ) :
    (coverEquiv φ g hg).symm (cartan B' h) = cartan B (g.symm h) := by
  rw [LinearEquiv.symm_apply_eq, coverEquiv_cartan, LinearEquiv.apply_symm_apply]

/-- The inverse of the action of a sign-cover lift sends the root vector `x_b` to
`s_φ(g⁻¹ b) x_(g⁻¹ b)`. -/
@[simp]
theorem coverEquiv_symm_root (b : B'.normTwoShell) :
    (coverEquiv φ g hg).symm (root B' b) =
      SignCover.sectionSign φ ((normTwoShellEquivOfIsometry g hg).symm b) •
        root B ((normTwoShellEquivOfIsometry g hg).symm b) := by
  rw [LinearEquiv.symm_apply_eq, map_zsmul_unit, coverEquiv_root, Equiv.apply_symm_apply,
    smul_smul, Int.units_mul_self, one_smul]

variable {φ}

/-- **The image of a root bracket** under the action of a compatible sign-cover lift `(φ, g)`:
`⁅x_a, x_b⁆ ↦ s_φ(a) s_φ(b) ⁅x_(g a), x_(g b)⁆`. -/
theorem coverEquiv_rootBracket
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) (a b : B.normTwoShell) :
    coverEquiv φ g hg (rootBracket B a b) =
      (SignCover.sectionSign φ a * SignCover.sectionSign φ b) •
        rootBracket B' (normTwoShellEquivOfIsometry g hg a)
          (normTwoShellEquivOfIsometry g hg b) := by
  have key := SignCover.negOnePow_orderedSignForm_mul_sectionSign_add φ (g := g.toLinearMap)
    hinl hright a b
  simp only [LinearEquiv.coe_coe] at key
  have hsum : (normTwoShellEquivOfIsometry g hg a : J → ℤ) + normTwoShellEquivOfIsometry g hg b =
      g ((a : I → ℤ) + b) := by
    simp
  by_cases hm : (a : I → ℤ) + b ∈ B.normTwoShell
  · have hm' : (normTwoShellEquivOfIsometry g hg a : J → ℤ) + normTwoShellEquivOfIsometry g hg b ∈
        B'.normTwoShell := by
      rwa [hsum, apply_mem_normTwoShell_iff hg]
    have hroot : normTwoShellEquivOfIsometry g hg ⟨_, hm⟩ = ⟨_, hm'⟩ :=
      Subtype.ext <| by rw [coe_normTwoShellEquivOfIsometry_apply]; exact hsum.symm
    rw [rootBracket_of_mem hm, rootBracket_of_mem hm', map_zsmul_unit, coverEquiv_root, hroot,
      smul_smul, smul_smul]
    congr 1
    simp only [coe_normTwoShellEquivOfIsometry_apply]
    rw [key]
    ac_rfl
  by_cases hz : (a : I → ℤ) + b = 0
  · have hz' : (normTwoShellEquivOfIsometry g hg a : J → ℤ) + normTwoShellEquivOfIsometry g hg b =
        0 := by
      rw [hsum, hz, map_zero]
    rw [hz, SignCover.sectionSign_zero, mul_one] at key
    rw [rootBracket_of_add_eq_zero hz, rootBracket_of_add_eq_zero hz', map_zsmul_unit,
      coverEquiv_cartan, smul_smul, coe_normTwoShellEquivOfIsometry_apply,
      coe_normTwoShellEquivOfIsometry_apply, key, mul_comm]
  · have hz' : (normTwoShellEquivOfIsometry g hg a : J → ℤ) + normTwoShellEquivOfIsometry g hg b ≠
        0 := by
      rwa [hsum, map_ne_zero_iff _ g.injective]
    have hm' : (normTwoShellEquivOfIsometry g hg a : J → ℤ) + normTwoShellEquivOfIsometry g hg b ∉
        B'.normTwoShell := by
      rwa [hsum, apply_mem_normTwoShell_iff hg]
    rw [rootBracket_of_notMem_of_add_ne_zero hm hz, rootBracket_of_notMem_of_add_ne_zero hm' hz',
      map_zero, smul_zero]

/-- **A compatible sign-cover lift preserves the bracket.** If `φ` fixes the kernel `ℤˣ` and lies
over the isometry `g`, then `Matrix.ShellLieAlgebra.coverEquiv φ g` preserves the bracket. -/
theorem coverEquiv_lie
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) (x y : ShellLieAlgebra B) :
    coverEquiv φ g hg ⁅x, y⁆ = ⁅coverEquiv φ g hg x, coverEquiv φ g hg y⁆ := by
  have hpair (h : I → ℤ) (b : B.normTwoShell) :
      g h ⬝ᵥ B' *ᵥ (normTwoShellEquivOfIsometry g hg b : J → ℤ) = h ⬝ᵥ B *ᵥ (b : I → ℤ) := by
    rw [coe_normTwoShellEquivOfIsometry_apply, hg]
  have key : (bracketBilin B).compr₂ (coverEquiv φ g hg).toLinearMap =
      (bracketBilin B').compl₁₂ (coverEquiv φ g hg).toLinearMap
        (coverEquiv φ g hg).toLinearMap :=
    (basis B).ext fun i => (basis B).ext fun j => by
      classical
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        bracketBilin_apply_apply]
      rcases i with i | a <;> rcases j with j | b
      · simp
      · simp only [basis_inl, basis_inr, cartan_lie_root, map_zsmul, coverEquiv_cartan,
          coverEquiv_root, ShellLieAlgebra.lie_units_smul, hpair]
        exact smul_comm _ _ _
      · simp only [basis_inl, basis_inr, root_lie_cartan, map_neg, map_zsmul, coverEquiv_cartan,
          coverEquiv_root, ShellLieAlgebra.units_smul_lie, hpair, smul_neg]
        rw [smul_comm]
      · simp only [basis_inr, root_lie_root, coverEquiv_root, ShellLieAlgebra.units_smul_lie,
          ShellLieAlgebra.lie_units_smul, coverEquiv_rootBracket g hg hinl hright, smul_smul,
          mul_comm]
  simpa using congr($key x y)

/-- **The identity pair acts by the identity.** -/
@[simp]
theorem coverEquiv_id :
    coverEquiv (MonoidHom.id (SignCover B)) (LinearEquiv.refl ℤ (I → ℤ)) (by simp) =
      LinearEquiv.refl ℤ _ := by
  refine (basis B).ext' fun k => ?_
  rcases k with i | a
  · classical
    rw [basis_inl, coverEquiv_cartan, LinearEquiv.refl_apply, LinearEquiv.refl_apply]
  · rw [basis_inr, coverEquiv_root, SignCover.sectionSign_id, one_smul]
    congr 1
    ext
    simp

/-- **Composite pairs act by composites.** If `φ` lies over `g` and `ψ` fixes the kernel `ℤˣ`,
then the action of `(ψ ∘ φ, g' ∘ g)` is the action of `(φ, g)` followed by that of `(ψ, g')`. -/
theorem coverEquiv_trans (ψ : SignCover B' →* SignCover B'') (g' : (J → ℤ) ≃ₗ[ℤ] (K → ℤ))
    (hg' : ∀ a b, g' a ⬝ᵥ B'' *ᵥ g' b = a ⬝ᵥ B' *ᵥ b)
    (hinl : ∀ u, ψ (FactorSet.inl (signFactorSet B') u) = FactorSet.inl (signFactorSet B'') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) :
    (coverEquiv φ g hg).trans (coverEquiv ψ g' hg') =
      coverEquiv (ψ.comp φ) (g.trans g') (fun a b => by simp [hg', hg]) := by
  refine (basis B).ext' fun k => ?_
  rcases k with i | a
  · classical
    simp
  · rw [basis_inr, LinearEquiv.trans_apply, coverEquiv_root, map_zsmul_unit, coverEquiv_root,
      coverEquiv_root, smul_smul,
      SignCover.sectionSign_comp ψ φ (g := g.toLinearMap) hinl hright,
      coe_normTwoShellEquivOfIsometry_apply]
    congr 2
    ext
    simp

/-- **The action of compatible sign-cover lifts is faithful.** If the norm-two shell of `B` spans
its Gram lattice, as it does when the diagonal entries of `B` are `2`, a compatible pair `(φ, g)`
of an endomorphism `φ` of the ordered sign cover and an isometry `g` of the Gram lattice acts on
`ShellLieAlgebra B` by the identity exactly when `φ` and `g` are identities. -/
theorem coverEquiv_eq_refl_iff (hspan : Submodule.span ℤ B.normTwoShell = ⊤)
    {φ : SignCover B →* SignCover B} {g : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (hg : ∀ a b, g a ⬝ᵥ B *ᵥ g b = a ⬝ᵥ B *ᵥ b)
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B) u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) :
    coverEquiv φ g hg = LinearEquiv.refl ℤ _ ↔
      φ = MonoidHom.id _ ∧ g = LinearEquiv.refl ℤ _ := by
  refine ⟨fun h => ?_, fun ⟨hφ, hg'⟩ => by subst hφ hg'; exact coverEquiv_id⟩
  -- The Cartan vectors detect `g`.
  have hg1 : g = LinearEquiv.refl ℤ _ := LinearEquiv.ext fun v => by
    simpa using congr((equivProd B ($h (cartan B v))).1)
  subst hg1
  refine ⟨SignCover.eq_id_of_sectionSign_eq_one hinl (fun x => by simp [hright]) hspan
    fun a ha => ?_, rfl⟩
  -- The root vector `x_a` is moved to `s_φ(a) x_a`, so `s_φ(a) = 1` on the shell.
  have hroot : normTwoShellEquivOfIsometry (LinearEquiv.refl ℤ (I → ℤ)) hg ⟨a, ha⟩ = ⟨a, ha⟩ :=
    Subtype.ext (by simp)
  have key := congr((equivProd B ($h (root B ⟨a, ha⟩))).2 ⟨a, ha⟩)
  rw [coverEquiv_root, hroot] at key
  simpa [Units.smul_def, Units.val_eq_one] using key

/-- **The action of a compatible sign-cover lift as an isomorphism of Lie algebras.** For positive
definite `B` and `B'` with even diagonals, the linear equivalence
`Matrix.ShellLieAlgebra.coverEquiv φ g` of a homomorphism `φ` of ordered sign covers fixing the
kernel `ℤˣ` and lying over the isometry `g` is an isomorphism of the signed Lie rings of `B` and
`B'`. -/
noncomputable def coverLieEquiv (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) (hB' : B'.PosDef)
    (hdiag' : ∀ j, Even (B' j j))
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) :
    letI := lieRing hB hdiag
    letI := lieRing hB' hdiag'
    ShellLieAlgebra B ≃ₗ⁅ℤ⁆ ShellLieAlgebra B' :=
  letI := lieRing hB hdiag
  letI := lieRing hB' hdiag'
  { coverEquiv φ g hg with
    map_lie' := coverEquiv_lie g hg hinl hright _ _ }

@[simp]
theorem coverLieEquiv_apply (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) (hB' : B'.PosDef)
    (hdiag' : ∀ j, Even (B' j j))
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) (x : ShellLieAlgebra B) :
    coverLieEquiv g hg hB hdiag hB' hdiag' hinl hright x = coverEquiv φ g hg x :=
  (rfl)

end Matrix.ShellLieAlgebra
