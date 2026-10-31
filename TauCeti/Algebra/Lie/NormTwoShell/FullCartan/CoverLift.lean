/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Basic
public import TauCeti.Algebra.Lie.NormTwoShell.Reindex
public import TauCeti.LinearAlgebra.Matrix.Reindex
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# Cover lifts and relabellings over a full Cartan lattice

Let `D : Matrix.ShellCartanDatum B Y` and `D' : Matrix.ShellCartanDatum B' Y'` be full Cartan
lattices for the norm-two shells of Gram matrices `B` and `B'` on linearly ordered finite sets, so
that `Matrix.FullShellLieAlgebra D` is the signed Lie algebra with Cartan part `Y` and root vectors
`x_a` for the vectors `a` of the norm-two shell of `B`. A symmetry of the signed shell Lie algebra
`Matrix.ShellLieAlgebra B` is given by a homomorphism `φ` of ordered sign covers fixing the kernel
`ℤˣ` and lying over an isometry `g` of the Gram lattices
(`Matrix.ShellLieAlgebra.coverEquiv`). Over a full Cartan lattice the Cartan part `Y` is no longer
determined by the root lattice, so such a symmetry needs in addition a linear equivalence
`γ : Y ≃ₗ[ℤ] Y'` compatible with the datum:

`γ (a∨) = (g a)∨`  and  `⟨g a, γ y⟩' = ⟨a, y⟩`

for every lattice vector `a` and every `y : Y`. This file constructs the resulting linear
equivalence `Matrix.FullShellLieAlgebra.coverEquiv D D' φ g hg γ`,

`H_y ↦ H_(γ y)`,  `x_a ↦ s_φ(a) x_(g a)`,

with `s_φ` the section signs of `φ`, and proves that it preserves the bracket
(`Matrix.FullShellLieAlgebra.coverEquiv_lie`). It is compatible with the comparison map
`Matrix.FullShellLieAlgebra.toFull` from the shell algebra (`coverEquiv_toFull`), and it is
functorial in the triple `(φ, g, γ)`.

The main instance is the pinned action of a relabelling `e : I ≃ J` with `B.reindex e e = B'`, for
instance a diagram automorphism `σ` of a simply laced Dynkin diagram:
`Matrix.FullShellLieAlgebra.reindex`, `H_y ↦ H_(γ y)` and `x_a ↦ σ_e(a) x_(a ∘ e.symm)` with the
inversion sign `σ_e = Matrix.inversionSign B e`. For symmetric `B` it is the action of the
relabelled ordered sign cover (`Matrix.FullShellLieAlgebra.reindex_eq_coverEquiv`), and it extends
the pinned action `Matrix.ShellLieAlgebra.reindex` on the coroot lattice along `toFull`
(`Matrix.FullShellLieAlgebra.reindex_toFull`). For a diagram automorphism its powers are the
pinned actions of the powers of `σ` and `γ`, so it has finite order whenever `σ` and `γ` do
(`Matrix.FullShellLieAlgebra.reindex_pow`, `Matrix.FullShellLieAlgebra.reindex_iterate_eq_id`).
No splitting of `Y` into central and coroot summands is used, and `Y` may have torsion.

## Main definitions

* `Matrix.FullShellLieAlgebra.signedCongr`: the linear equivalence `H_y ↦ H_(γ y)`,
  `x_a ↦ s(a) x_(e a)` for a bijection `e` of norm-two shells and signs `s`, of which the two
  actions below are instances.
* `Matrix.FullShellLieAlgebra.coverEquiv`: the action `H_y ↦ H_(γ y)`, `x_a ↦ s_φ(a) x_(g a)`.
* `Matrix.FullShellLieAlgebra.coverLieEquiv`: the same map as an isomorphism of Lie algebras, for
  positive definite Gram matrices with even diagonal.
* `Matrix.FullShellLieAlgebra.reindex`: the pinned action of a relabelling of the vertices.
* `Matrix.FullShellLieAlgebra.reindexLieEquiv`: the same map as an isomorphism of Lie algebras.

## Main results

* `Matrix.FullShellLieAlgebra.coverEquiv_cartan`, `Matrix.FullShellLieAlgebra.coverEquiv_root`:
  the values on Cartan and root vectors.
* `Matrix.FullShellLieAlgebra.coverEquiv_toFull`: compatibility with the shell algebra.
* `Matrix.FullShellLieAlgebra.coverEquiv_lie`: a compatible triple preserves the bracket.
* `Matrix.FullShellLieAlgebra.coverEquiv_id`, `Matrix.FullShellLieAlgebra.coverEquiv_trans`:
  functoriality.
* `Matrix.FullShellLieAlgebra.reindex_cartan`, `Matrix.FullShellLieAlgebra.reindex_root`,
  `Matrix.FullShellLieAlgebra.reindex_eq_coverEquiv`,
  `Matrix.FullShellLieAlgebra.reindex_toFull`, `Matrix.FullShellLieAlgebra.reindex_rootBracket`,
  `Matrix.FullShellLieAlgebra.reindex_lie`: the corresponding statements for relabellings.
* `Matrix.FullShellLieAlgebra.reindex_root_single`,
  `Matrix.FullShellLieAlgebra.reindex_root_neg_single`: the pinned action preserves the simple
  root vectors.
* `Matrix.FullShellLieAlgebra.reindex_pow`, `Matrix.FullShellLieAlgebra.reindex_iterate_eq_id`:
  powers of the pinned action of a diagram automorphism.

## References

* I. B. Frenkel, J. Lepowsky and A. Meurman, *Vertex operator algebras and the Monster*, Academic
  Press (1988), §§5.4 and 6.4, for automorphisms of the central extension of a lattice lying over
  lattice isometries and their action on the associated Lie algebra.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, American Mathematical
  Society (2003), Part II, Chapter 1, for the Lie algebra of a split reductive group as the Lie
  algebra of its maximal torus, spanned by the cocharacter lattice, together with the root
  spaces.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, Cambridge University Press (1990),
  §7.8.
-/

public section

namespace Matrix.FullShellLieAlgebra

open TauCeti Module

attribute [local instance] trivialMulDistribMulAction

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] {B : Matrix I I ℤ}
  {B' : Matrix J J ℤ} {B'' : Matrix K K ℤ} {Y Y' Y'' : Type*} [AddCommGroup Y] [AddCommGroup Y']
  [AddCommGroup Y'']
  (D : ShellCartanDatum B Y) (D' : ShellCartanDatum B' Y') (D'' : ShellCartanDatum B'' Y'')

section SignedCongr

variable (γ : Y ≃ₗ[ℤ] Y') (e : B.normTwoShell ≃ B'.normTwoShell) (s : B.normTwoShell → ℤˣ)

/-- **Signed relabelling of a full shell Lie algebra.** For a linear equivalence `γ : Y ≃ₗ[ℤ] Y'`
of full Cartan lattices, a bijection `e` of norm-two shells and signs `s`, the linear equivalence
`FullShellLieAlgebra D ≃ₗ[ℤ] FullShellLieAlgebra D'` sending the Cartan vector `H_y` to `H_(γ y)`
and the root vector `x_a` to `s(a) x_(e a)`. Both `Matrix.FullShellLieAlgebra.coverEquiv` and
`Matrix.FullShellLieAlgebra.reindex` are of this form. -/
noncomputable def signedCongr : FullShellLieAlgebra D ≃ₗ[ℤ] FullShellLieAlgebra D' :=
  equivProd D ≪≫ₗ
    γ.prodCongr (Finsupp.basisSingleOne.equiv (Finsupp.basisSingleOne.unitsSMul (s ∘ e.symm)) e) ≪≫ₗ
    (equivProd D').symm

/-- A signed relabelling sends the Cartan vector `H_y` to `H_(γ y)`. -/
@[simp]
theorem signedCongr_cartan (y : Y) : signedCongr D D' γ e s (cartan D y) = cartan D' (γ y) := by
  apply (equivProd D').injective
  simp [signedCongr]

/-- A signed relabelling sends the root vector `x_a` to `s(a) x_(e a)`. -/
@[simp]
theorem signedCongr_root (a : B.normTwoShell) :
    signedCongr D D' γ e s (root D a) = s a • root D' (e a) := by
  apply (equivProd D').injective
  simp only [signedCongr, LinearEquiv.trans_apply, equivProd_root, LinearEquiv.prodCongr_apply,
    map_zero, LinearEquiv.apply_symm_apply, map_zsmul_unit, Prod.smul_mk, smul_zero]
  rw [← congrFun Finsupp.coe_basisSingleOne a, Basis.equiv_apply, Basis.unitsSMul_apply,
    Function.comp_apply, Equiv.symm_apply_apply, Finsupp.coe_basisSingleOne]

/-- The inverse of a signed relabelling sends the Cartan vector `H_y` to `H_(γ⁻¹ y)`. -/
@[simp]
theorem signedCongr_symm_cartan (y : Y') :
    (signedCongr D D' γ e s).symm (cartan D' y) = cartan D (γ.symm y) := by
  rw [LinearEquiv.symm_apply_eq, signedCongr_cartan, LinearEquiv.apply_symm_apply]

/-- The inverse of a signed relabelling sends the root vector `x_b` to `s(e⁻¹ b) x_(e⁻¹ b)`. -/
@[simp]
theorem signedCongr_symm_root (b : B'.normTwoShell) :
    (signedCongr D D' γ e s).symm (root D' b) = s (e.symm b) • root D (e.symm b) := by
  rw [LinearEquiv.symm_apply_eq, map_zsmul_unit, signedCongr_root, Equiv.apply_symm_apply,
    smul_smul, Int.units_mul_self, one_smul]

variable {D D' γ e s} [LinearOrder I] in
/-- **A signed relabelling extends a matching map of shell algebras.** If a linear map
`f : ShellLieAlgebra B →ₗ[ℤ] ShellLieAlgebra B'` sends `H_h` to `H_(g h)` and `x_a` to
`s(a) x_(e a)`, and `γ` carries each coroot `h∨` of `D` to the coroot `(g h)∨` of `D'`, then the
signed relabelling extends `f` along `toFull`. -/
theorem signedCongr_toFull (g : (I → ℤ) → (J → ℤ)) {f : ShellLieAlgebra B →ₗ[ℤ] ShellLieAlgebra B'}
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (g h))
    (hcartan : ∀ h, f (ShellLieAlgebra.cartan B h) = ShellLieAlgebra.cartan B' (g h))
    (hroot : ∀ a, f (ShellLieAlgebra.root B a) = s a • ShellLieAlgebra.root B' (e a))
    (x : ShellLieAlgebra B) :
    signedCongr D D' γ e s (toFull D x) = toFull D' (f x) := by
  have key : (signedCongr D D' γ e s).toLinearMap ∘ₗ toFull D = toFull D' ∘ₗ f :=
    (ShellLieAlgebra.basis B).ext fun i => by
      classical
      rcases i with i | a <;>
        simp [ShellLieAlgebra.basis_inl, ShellLieAlgebra.basis_inr, hc, hcartan, hroot]
  exact congr($key x)

end SignedCongr

variable [LinearOrder I] [LinearOrder J] [LinearOrder K]

section CoverEquiv

variable (φ : SignCover B →* SignCover B') (g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ))
  (hg : ∀ a b, g a ⬝ᵥ B' *ᵥ g b = a ⬝ᵥ B *ᵥ b) (γ : Y ≃ₗ[ℤ] Y')

/-- **The action of a sign-cover lift over a full Cartan lattice.** For an isometry
`g : (I → ℤ) ≃ₗ[ℤ] (J → ℤ)` of the Gram lattices of `B` and `B'`, a homomorphism
`φ : SignCover B →* SignCover B'` of ordered sign covers and a linear equivalence `γ : Y ≃ₗ[ℤ] Y'`
of full Cartan lattices, the linear equivalence `FullShellLieAlgebra D ≃ₗ[ℤ] FullShellLieAlgebra D'`
sending the Cartan vector `H_y` to `H_(γ y)` and the root vector `x_a` to `s_φ(a) x_(g a)`, where
`s_φ` is the section sign `Matrix.SignCover.sectionSign φ`. It preserves the bracket when `φ` fixes
the kernel `ℤˣ` and lies over `g`, and `γ` is compatible with the coroots and root weights
(`Matrix.FullShellLieAlgebra.coverEquiv_lie`). -/
noncomputable def coverEquiv : FullShellLieAlgebra D ≃ₗ[ℤ] FullShellLieAlgebra D' :=
  signedCongr D D' γ (normTwoShellEquivOfIsometry g hg) fun a => SignCover.sectionSign φ a

/-- The action of a sign-cover lift sends the Cartan vector `H_y` to `H_(γ y)`. -/
@[simp]
theorem coverEquiv_cartan (y : Y) :
    coverEquiv D D' φ g hg γ (cartan D y) = cartan D' (γ y) :=
  signedCongr_cartan ..

/-- The action of a sign-cover lift sends the root vector `x_a` to `s_φ(a) x_(g a)`. -/
@[simp]
theorem coverEquiv_root (a : B.normTwoShell) :
    coverEquiv D D' φ g hg γ (root D a) =
      SignCover.sectionSign φ a • root D' (normTwoShellEquivOfIsometry g hg a) :=
  signedCongr_root ..

/-- The inverse of the action of a sign-cover lift sends the Cartan vector `H_y` to
`H_(γ⁻¹ y)`. -/
@[simp]
theorem coverEquiv_symm_cartan (y : Y') :
    (coverEquiv D D' φ g hg γ).symm (cartan D' y) = cartan D (γ.symm y) :=
  signedCongr_symm_cartan ..

/-- The inverse of the action of a sign-cover lift sends the root vector `x_b` to
`s_φ(g⁻¹ b) x_(g⁻¹ b)`. -/
@[simp]
theorem coverEquiv_symm_root (b : B'.normTwoShell) :
    (coverEquiv D D' φ g hg γ).symm (root D' b) =
      SignCover.sectionSign φ ((normTwoShellEquivOfIsometry g hg).symm b) •
        root D ((normTwoShellEquivOfIsometry g hg).symm b) :=
  signedCongr_symm_root ..

variable {D D' φ g γ}

/-- **Compatibility with the shell algebra.** If `γ` carries each coroot `h∨` of `D` to the coroot
`(g h)∨` of `D'`, then the action of `(φ, g, γ)` on the full algebras extends the action
`Matrix.ShellLieAlgebra.coverEquiv φ g` on the shell algebras along `toFull`. -/
theorem coverEquiv_toFull (hc : ∀ h, γ (D.coroot h) = D'.coroot (g h))
    (x : ShellLieAlgebra B) :
    coverEquiv D D' φ g hg γ (toFull D x) = toFull D' (ShellLieAlgebra.coverEquiv φ g hg x) :=
  signedCongr_toFull g (f := (ShellLieAlgebra.coverEquiv φ g hg).toLinearMap) hc
    (fun h => ShellLieAlgebra.coverEquiv_cartan φ g hg h)
    (fun a => ShellLieAlgebra.coverEquiv_root φ g hg a) x

/-- **The image of a root bracket** under the action of a compatible triple `(φ, g, γ)`:
`⁅x_a, x_b⁆ ↦ s_φ(a) s_φ(b) ⁅x_(g a), x_(g b)⁆`. -/
theorem coverEquiv_rootBracket
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd))
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (g h)) (a b : B.normTwoShell) :
    coverEquiv D D' φ g hg γ (rootBracket D a b) =
      (SignCover.sectionSign φ a * SignCover.sectionSign φ b) •
        rootBracket D' (normTwoShellEquivOfIsometry g hg a)
          (normTwoShellEquivOfIsometry g hg b) := by
  rw [← toFull_rootBracket, coverEquiv_toFull hg hc,
    ShellLieAlgebra.coverEquiv_rootBracket g hg hinl hright, map_zsmul_unit, toFull_rootBracket]

/-- **A compatible triple preserves the bracket.** If `φ` fixes the kernel `ℤˣ` and lies over the
isometry `g`, and `γ` carries coroots to coroots, `γ (h∨) = (g h)∨`, and root weights to root
weights, `⟨g a, γ y⟩' = ⟨a, y⟩`, then `Matrix.FullShellLieAlgebra.coverEquiv D D' φ g hg γ`
preserves the bracket. -/
theorem coverEquiv_lie
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd))
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (g h))
    (hw : ∀ a y, D'.weight (g a) (γ y) = D.weight a y) (x y : FullShellLieAlgebra D) :
    coverEquiv D D' φ g hg γ ⁅x, y⁆ = ⁅coverEquiv D D' φ g hg γ x, coverEquiv D D' φ g hg γ y⁆ := by
  have hw' (a : B.normTwoShell) (y : Y) :
      D'.weight (normTwoShellEquivOfIsometry g hg a) (γ y) = D.weight a y := by
    rw [coe_normTwoShellEquivOfIsometry_apply, hw]
  have key : (bracketBilin D).compr₂ (coverEquiv D D' φ g hg γ).toLinearMap =
      (bracketBilin D').compl₁₂ (coverEquiv D D' φ g hg γ).toLinearMap
        (coverEquiv D D' φ g hg γ).toLinearMap := by
    refine linearMap_ext (fun y => linearMap_ext (fun z => ?_) fun b => ?_)
      fun a => linearMap_ext (fun z => ?_) fun b => ?_ <;>
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        bracketBilin_apply_apply]
    · simp
    · simp only [cartan_lie_root, map_zsmul, coverEquiv_cartan, coverEquiv_root,
        FullShellLieAlgebra.lie_units_smul, hw']
      exact smul_comm _ _ _
    · simp only [root_lie_cartan, map_neg, map_zsmul, coverEquiv_cartan, coverEquiv_root,
        FullShellLieAlgebra.units_smul_lie, hw', smul_neg]
      rw [smul_comm]
    · simp only [root_lie_root, coverEquiv_root, FullShellLieAlgebra.units_smul_lie,
        FullShellLieAlgebra.lie_units_smul, coverEquiv_rootBracket hg hinl hright hc, smul_smul,
        mul_comm]
  simpa using congr($key x y)

variable (D) in
/-- **The identity triple acts by the identity.** -/
@[simp]
theorem coverEquiv_id :
    coverEquiv D D (MonoidHom.id (SignCover B)) (LinearEquiv.refl ℤ (I → ℤ)) (by simp)
      (LinearEquiv.refl ℤ Y) = LinearEquiv.refl ℤ _ := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext (fun y => by simp) fun a => ?_)
  rw [LinearEquiv.coe_coe, coverEquiv_root, SignCover.sectionSign_id, one_smul]
  congr 1
  ext
  simp

/-- **Composite triples act by composites.** If `φ` lies over `g` and `ψ` fixes the kernel `ℤˣ`,
then the action of `(ψ ∘ φ, g' ∘ g, γ' ∘ γ)` is the action of `(φ, g, γ)` followed by that of
`(ψ, g', γ')`. -/
theorem coverEquiv_trans (ψ : SignCover B' →* SignCover B'') (g' : (J → ℤ) ≃ₗ[ℤ] (K → ℤ))
    (hg' : ∀ a b, g' a ⬝ᵥ B'' *ᵥ g' b = a ⬝ᵥ B' *ᵥ b) (γ' : Y' ≃ₗ[ℤ] Y'')
    (hinl : ∀ u, ψ (FactorSet.inl (signFactorSet B') u) = FactorSet.inl (signFactorSet B'') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd)) :
    (coverEquiv D D' φ g hg γ).trans (coverEquiv D' D'' ψ g' hg' γ') =
      coverEquiv D D'' (ψ.comp φ) (g.trans g') (fun a b => by simp [hg', hg]) (γ.trans γ') := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext (fun y => by simp) fun a => ?_)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply, coverEquiv_root,
    map_zsmul_unit, coverEquiv_root, coverEquiv_root, smul_smul,
    SignCover.sectionSign_comp ψ φ (g := g.toLinearMap) hinl hright,
    coe_normTwoShellEquivOfIsometry_apply]
  congr 2
  ext
  simp

/-- **The action of a compatible triple as an isomorphism of Lie algebras.** For positive definite
`B` and `B'` with even diagonals, the linear equivalence
`Matrix.FullShellLieAlgebra.coverEquiv D D' φ g hg γ` of a homomorphism `φ` of ordered sign covers
fixing the kernel `ℤˣ` and lying over the isometry `g`, and of a linear equivalence `γ` compatible
with the coroots and root weights, is an isomorphism of the signed Lie rings over the full Cartan
lattices. -/
noncomputable def coverLieEquiv (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) (hB' : B'.PosDef)
    (hdiag' : ∀ j, Even (B' j j))
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd))
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (g h))
    (hw : ∀ a y, D'.weight (g a) (γ y) = D.weight a y) :
    letI := lieRing D hB hdiag
    letI := lieRing D' hB' hdiag'
    FullShellLieAlgebra D ≃ₗ⁅ℤ⁆ FullShellLieAlgebra D' :=
  letI := lieRing D hB hdiag
  letI := lieRing D' hB' hdiag'
  { coverEquiv D D' φ g hg γ with
    map_lie' := coverEquiv_lie hg hinl hright hc hw _ _ }

@[simp]
theorem coverLieEquiv_apply (hB : B.PosDef) (hdiag : ∀ i, Even (B i i)) (hB' : B'.PosDef)
    (hdiag' : ∀ j, Even (B' j j))
    (hinl : ∀ u, φ (FactorSet.inl (signFactorSet B) u) = FactorSet.inl (signFactorSet B') u)
    (hright : ∀ x, (φ x).right = .ofAdd (g x.right.toAdd))
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (g h))
    (hw : ∀ a y, D'.weight (g a) (γ y) = D.weight a y) (x : FullShellLieAlgebra D) :
    coverLieEquiv hg hB hdiag hB' hdiag' hinl hright hc hw x = coverEquiv D D' φ g hg γ x :=
  (rfl)

end CoverEquiv

section Reindex

variable (e : I ≃ J) (he : B.reindex e e = B') (γ : Y ≃ₗ[ℤ] Y')

/-- **The pinned action of a relabelling over a full Cartan lattice.** For a relabelling
`e : I ≃ J` of the vertices of `B` with `B.reindex e e = B'` and a linear equivalence
`γ : Y ≃ₗ[ℤ] Y'` of full Cartan lattices, the linear equivalence
`FullShellLieAlgebra D ≃ₗ[ℤ] FullShellLieAlgebra D'` sending the Cartan vector `H_y` to `H_(γ y)`
and the root vector `x_a` to `σ_e(a) x_(a ∘ e.symm)`, where `σ_e` is the inversion sign
`Matrix.inversionSign B e`. For symmetric `B` it is the action of the relabelled ordered sign cover
(`Matrix.FullShellLieAlgebra.reindex_eq_coverEquiv`), and it preserves the bracket when `γ` is
compatible with the coroots and root weights (`Matrix.FullShellLieAlgebra.reindex_lie`). For a
diagram automorphism `e = σ` it is the pinned automorphism of the full algebra attached to `σ` and
`γ`. -/
noncomputable def reindex : FullShellLieAlgebra D ≃ₗ[ℤ] FullShellLieAlgebra D' :=
  signedCongr D D' γ (normTwoShellCongr he) fun a => inversionSign B e a

/-- The pinned action of a relabelling sends the Cartan vector `H_y` to `H_(γ y)`. -/
@[simp]
theorem reindex_cartan (y : Y) : reindex D D' e he γ (cartan D y) = cartan D' (γ y) :=
  signedCongr_cartan ..

/-- The pinned action of a relabelling rescales the root vector `x_a` by the inversion sign and
moves it to the relabelled root: `x_a ↦ σ_e(a) x_(a ∘ e.symm)`. -/
@[simp]
theorem reindex_root (a : B.normTwoShell) :
    reindex D D' e he γ (root D a) = inversionSign B e a • root D' (normTwoShellCongr he a) :=
  signedCongr_root ..

/-- The inverse of the pinned action of a relabelling sends the Cartan vector `H_y` to
`H_(γ⁻¹ y)`. -/
@[simp]
theorem reindex_symm_cartan (y : Y') :
    (reindex D D' e he γ).symm (cartan D' y) = cartan D (γ.symm y) :=
  signedCongr_symm_cartan ..

/-- The inverse of the pinned action of a relabelling sends the root vector `x_b` to
`σ_e(b ∘ e) x_(b ∘ e)`. -/
@[simp]
theorem reindex_symm_root (b : B'.normTwoShell) :
    (reindex D D' e he γ).symm (root D' b) =
      inversionSign B e ((normTwoShellCongr he).symm b) • root D ((normTwoShellCongr he).symm b) :=
  signedCongr_symm_root ..

/-- The pinned action of a relabelling sends the simple root vector `x_(αᵢ)` to `x_(α_(e i))`. -/
theorem reindex_root_single [DecidableEq I] [DecidableEq J] (i : I)
    (hi : Pi.single i 1 ∈ B.normTwoShell) (hi' : Pi.single (e i) 1 ∈ B'.normTwoShell) :
    reindex D D' e he γ (root D ⟨Pi.single i 1, hi⟩) = root D' ⟨Pi.single (e i) 1, hi'⟩ := by
  rw [reindex_root, inversionSign_single, one_smul]
  congr 1
  exact Subtype.ext <| by rw [coe_normTwoShellCongr_apply, Pi.single_comp_equiv, Equiv.symm_symm]

/-- The pinned action of a relabelling sends the simple root vector `x_(-αᵢ)` to
`x_(-α_(e i))`. -/
theorem reindex_root_neg_single [DecidableEq I] [DecidableEq J] (i : I)
    (hi : -Pi.single i 1 ∈ B.normTwoShell) (hi' : -Pi.single (e i) 1 ∈ B'.normTwoShell) :
    reindex D D' e he γ (root D ⟨-Pi.single i 1, hi⟩) = root D' ⟨-Pi.single (e i) 1, hi'⟩ := by
  rw [reindex_root, inversionSign_neg, inversionSign_single, one_smul]
  congr 1
  exact Subtype.ext <| by
    rw [coe_normTwoShellCongr_apply, Pi.neg_comp, Pi.single_comp_equiv, Equiv.symm_symm]

/-- **The pinned action of a relabelling is the action of the relabelled sign cover.** For a
symmetric `B`, `Matrix.FullShellLieAlgebra.reindex D D' e he γ` is the action
`Matrix.FullShellLieAlgebra.coverEquiv` of the relabelling `Matrix.SignCover.reindex` of the
ordered sign covers, the isometry `a ↦ a ∘ e.symm`, and `γ`. -/
theorem reindex_eq_coverEquiv (hB : B.IsSymm) :
    reindex D D' e he γ =
      coverEquiv D D' (SignCover.reindex e hB he : SignCover B →* SignCover B')
        (LinearEquiv.funCongrLeft ℤ ℤ e.symm)
        (fun a b => by subst he; exact comp_equiv_symm_dotProduct_reindex_mulVec e B a b) γ := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext (fun y => by simp) fun a => ?_)
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, reindex_root, coverEquiv_root,
    SignCover.sectionSign_reindex, normTwoShellEquivOfIsometry_funCongrLeft he]

variable {D D' γ}

/-- **The pinned action extends the one on the coroot lattice.** If `γ` carries each coroot `h∨`
of `D` to the coroot `(h ∘ e.symm)∨` of `D'`, then the pinned action on the full algebras extends
the pinned action `Matrix.ShellLieAlgebra.reindex e he` on the shell algebras along `toFull`. -/
theorem reindex_toFull (hc : ∀ h, γ (D.coroot h) = D'.coroot (h ∘ e.symm))
    (x : ShellLieAlgebra B) :
    reindex D D' e he γ (toFull D x) = toFull D' (ShellLieAlgebra.reindex e he x) :=
  signedCongr_toFull (· ∘ e.symm) (f := (ShellLieAlgebra.reindex e he).toLinearMap) hc
    (fun h => ShellLieAlgebra.reindex_cartan e he h)
    (fun a => ShellLieAlgebra.reindex_root e he a) x

/-- **The pinned action of a relabelling of a root bracket**, for symmetric `B`, when `γ` carries
coroots to coroots: `⁅x_a, x_b⁆ ↦ σ_e(a) σ_e(b) ⁅x_(a ∘ e.symm), x_(b ∘ e.symm)⁆`. -/
theorem reindex_rootBracket (hB : B.IsSymm) (hc : ∀ h, γ (D.coroot h) = D'.coroot (h ∘ e.symm))
    (a b : B.normTwoShell) :
    reindex D D' e he γ (rootBracket D a b) =
      (inversionSign B e a * inversionSign B e b) •
        rootBracket D' (normTwoShellCongr he a) (normTwoShellCongr he b) := by
  rw [← toFull_rootBracket, reindex_toFull e he hc, ShellLieAlgebra.reindex_rootBracket e he hB,
    map_zsmul_unit, toFull_rootBracket]

/-- **The pinned action of a relabelling preserves the bracket**, for symmetric `B`, when `γ`
carries coroots to coroots, `γ (h∨) = (h ∘ e.symm)∨`, and root weights to root weights,
`⟨a ∘ e.symm, γ y⟩' = ⟨a, y⟩`. -/
theorem reindex_lie (hB : B.IsSymm) (hc : ∀ h, γ (D.coroot h) = D'.coroot (h ∘ e.symm))
    (hw : ∀ a y, D'.weight (a ∘ e.symm) (γ y) = D.weight a y) (x y : FullShellLieAlgebra D) :
    reindex D D' e he γ ⁅x, y⁆ = ⁅reindex D D' e he γ x, reindex D D' e he γ y⁆ := by
  have hfun (h : I → ℤ) : LinearEquiv.funCongrLeft ℤ ℤ e.symm h = h ∘ e.symm :=
    funext fun j => by
      rw [LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply, Function.comp_apply]
  rw [reindex_eq_coverEquiv D D' e he γ hB]
  exact coverEquiv_lie _ (fun u => by simp) (fun x => by simp [funext_iff, LinearMap.funLeft_apply])
    (fun h => by rw [hc, hfun]) (fun a y => by rw [hfun, hw]) x y

variable (D) in
/-- **The identity relabels the full algebra by the identity.** -/
@[simp]
theorem reindex_refl :
    reindex D D (Equiv.refl I) (by simp) (LinearEquiv.refl ℤ Y) = LinearEquiv.refl ℤ _ := by
  refine LinearEquiv.toLinearMap_injective (linearMap_ext (fun y => by simp) fun a => ?_)
  simp only [LinearEquiv.coe_coe, reindex_root, inversionSign_refl, one_smul,
    LinearEquiv.refl_apply]
  congr 1
  exact Subtype.ext (by simp)

/-- **Pinned actions of relabellings compose**, for symmetric `B`. -/
theorem reindex_trans (hB : B.IsSymm) (f : J ≃ K) (hf : B'.reindex f f = B'')
    (γ' : Y' ≃ₗ[ℤ] Y'') :
    (reindex D D' e he γ).trans (reindex D' D'' f hf γ') =
      reindex D D'' (e.trans f) (by rw [← hf, ← he]; ext; simp) (γ.trans γ') := by
  subst he hf
  refine LinearEquiv.toLinearMap_injective (linearMap_ext (fun y => ?_) fun a => ?_)
  · rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply, reindex_cartan,
      reindex_cartan, reindex_cartan, LinearEquiv.trans_apply]
  rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.trans_apply, reindex_root,
    map_zsmul_unit, reindex_root, reindex_root, smul_smul, coe_normTwoShellCongr_apply,
    inversionSign_trans B e hB f]
  congr 2
  apply Subtype.ext
  rw [coe_normTwoShellCongr_apply, coe_normTwoShellCongr_apply, coe_normTwoShellCongr_apply,
    Equiv.symm_trans, Equiv.coe_trans, Function.comp_assoc]

/-- **The pinned action of a relabelling as an isomorphism of Lie algebras.** For positive definite
`B` with even diagonal and `γ` compatible with the coroots and root weights, the pinned action
`Matrix.FullShellLieAlgebra.reindex` is an isomorphism of the signed Lie rings over the full Cartan
lattices of `D` and `D'`, where `B' = B.reindex e e` is again positive definite with even
diagonal. -/
noncomputable def reindexLieEquiv (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (h ∘ e.symm))
    (hw : ∀ a y, D'.weight (a ∘ e.symm) (γ y) = D.weight a y) :
    letI := lieRing D hB hdiag
    letI := lieRing D' (he ▸ hB.submatrix e.symm.injective) fun j => by
      simpa [← he] using hdiag (e.symm j)
    FullShellLieAlgebra D ≃ₗ⁅ℤ⁆ FullShellLieAlgebra D' :=
  letI := lieRing D hB hdiag
  letI := lieRing D' (he ▸ hB.submatrix e.symm.injective) fun j => by
    simpa [← he] using hdiag (e.symm j)
  { reindex D D' e he γ with
    map_lie' := reindex_lie e he hB.isHermitian.isSymm hc hw _ _ }

@[simp]
theorem reindexLieEquiv_apply (hB : B.PosDef) (hdiag : ∀ i, Even (B i i))
    (hc : ∀ h, γ (D.coroot h) = D'.coroot (h ∘ e.symm))
    (hw : ∀ a y, D'.weight (a ∘ e.symm) (γ y) = D.weight a y) (x : FullShellLieAlgebra D) :
    reindexLieEquiv e he hB hdiag hc hw x = reindex D D' e he γ x :=
  (rfl)

end Reindex

section Pow

variable (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B) (γ : Y ≃ₗ[ℤ] Y)

/-- **Powers of the pinned action of a diagram automorphism** are the pinned actions of the powers
of the vertex permutation `σ` and of the Cartan automorphism `γ`, for symmetric `B`. -/
theorem reindex_pow (hB : B.IsSymm) (n : ℕ) :
    reindex D D σ hσ γ ^ n = reindex D D (σ ^ n) (B.reindex_pow_eq_self σ σ hσ n) (γ ^ n) := by
  induction n with
  | zero => exact (reindex_refl D).symm
  | succ n ih =>
    rw [pow_succ', ih, LinearEquiv.mul_eq_trans, reindex_trans (hB := hB)]
    simp only [Equiv.Perm.mul_def, pow_succ', LinearEquiv.mul_eq_trans]

/-- **The pinned action of a diagram automorphism has finite order** when the vertex permutation
and the Cartan automorphism do: for symmetric `B`, if `σ ^ n = 1` and `γ ^ n = 1`, then the
`n`-th iterate of the pinned action is the identity. -/
theorem reindex_iterate_eq_id (hB : B.IsSymm) {n : ℕ} (hσn : σ ^ n = 1) (hγn : γ ^ n = 1) :
    (reindex D D σ hσ γ)^[n] = id := by
  have key : ∀ (τ : Equiv.Perm I) (hτ : B.reindex τ τ = B), τ = 1 → reindex D D τ hτ 1 = 1 := by
    rintro τ hτ rfl
    exact reindex_refl D
  rw [← LinearEquiv.coe_pow, reindex_pow D σ hσ γ hB, hγn, key _ _ hσn, LinearEquiv.coe_one]

end Pow

end Matrix.FullShellLieAlgebra
