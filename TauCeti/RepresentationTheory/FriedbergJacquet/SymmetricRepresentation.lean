/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.Algebra.CharP.Invertible
public import TauCeti.LinearAlgebra.Charpoly.Comp
public import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace.Isometry

/-!
# The symmetric representation of the unitary Friedberg–Jacquet pair and its contractions

Let `(W₁, h₁)` and `(W₂, h₂)` be finite-dimensional signed hermitian spaces of the same sign over a
field `K` with involution `σ`, for instance hermitian spaces over a quadratic extension `E/F`, and
let `W = W₁ ⊥ W₂` be their orthogonal sum. The involution `θ = Ad(1, -1)` of the unitary group
`U(W)` fixes `U(W₁) × U(W₂)`, and its `(-1)`-eigenspace in the Lie algebra `𝔲(W)` of
skew-adjoint endomorphisms of `W` is the *infinitesimal symmetric space* of the pair
`(U(W), U(W₁) × U(W₂))`. This file identifies it with `Hom(W₂, W₁)` and defines the two signed
contractions to the self-adjoint endomorphisms of `W₁` and of `W₂`.

* **The symmetric representation.** `U(W₁) × U(W₂)` acts on `Hom(W₂, W₁)` by
  `(g₁, g₂) • X = g₁ X g₂⁻¹` (`TauCeti.FriedbergJacquet.homRepresentation`), and the adjoint
  `X^τ : W₁ → W₂` of `TauCeti.signedHermitianHomAdjoint` transforms by
  `(g₁ X g₂⁻¹)^τ = g₂ X^τ g₁⁻¹`.
* **The block embedding.** `X ↦ δ(X) = [[0, X], [-X^τ, 0]]` is a linear isomorphism, over any
  ring of scalars `F` fixed by `σ`, from `Hom(W₂, W₁)` onto the infinitesimal symmetric space,
  with inverse the top-right block; it intertwines the symmetric representation with conjugation by
  `diag(g₁, g₂)`. Characteristic `2` must be excluded: there `θ` is the identity, so every
  skew-adjoint endomorphism, the identity of `W` for instance, lies in its `(-1)`-eigenspace.
* **The signed contractions.** `r₁(X) = -X X^τ` and `r₂(X) = -X^τ X` are self-adjoint
  endomorphisms of `W₁` and `W₂`; `r₁` is `U(W₁)`-equivariant and `U(W₂)`-invariant, `r₂` the
  reverse, and `r₂(X) = r₁(X^τ)`. The characteristic polynomials of `r₁(X)` and `r₂(X)` agree up
  to a power of `X`, and are equal when `W₁` and `W₂` have the same dimension. Between standard
  hermitian spaces `r₁(A) = -A Aᴴ` and `r₂(A) = -Aᴴ A`, with `Aᴴ` the conjugate transpose.

The sign of the contraction matters: for the standard rank-one hermitian forms and `X = 1`,
`δ(X)² = -1` and `r₁(X) = -1`, whereas the unsigned Gram map `X ↦ X X^τ` would give `1`.

Here `K` is a field, which covers a quadratic field extension `E/F`. The split quadratic algebra
`F × F` is not a field; its coordinate model, with Hom maps the pairs `(A, B)` and signed
contraction `-(A * B)`, is in `TauCeti/RepresentationTheory/FriedbergJacquet/SplitInvariants.lean`.

## Main definitions

* `TauCeti.FriedbergJacquet.homRepresentation`: the representation `(g₁, g₂) • X = g₁ X g₂⁻¹`.
* `TauCeti.FriedbergJacquet.offDiagonalBlock`: the block endomorphism `δ(X) = [[0, X], [-X^τ, 0]]`.
* `TauCeti.FriedbergJacquet.blockInvolution`: the involution `θ = Ad(1, -1)` of `End(W₁ × W₂)`.
* `TauCeti.FriedbergJacquet.infinitesimalSymmetricSpace`: the `(-1)`-eigenspace of `θ` in `𝔲(W)`.
* `TauCeti.FriedbergJacquet.homEquivInfinitesimalSymmetricSpace`: the isomorphism `X ↦ δ(X)`.
* `TauCeti.FriedbergJacquet.leftContraction`, `TauCeti.FriedbergJacquet.rightContraction`: the
  signed contractions `r₁` and `r₂`.

## References

* S. Leslie, *The endoscopic fundamental lemma for unitary Friedberg–Jacquet periods*,
  Ann. of Math. 201 (2025), 551–645, arXiv:1911.07907, §2.1 (the off-diagonal representation and
  the contractions, equation (2.1)).
* S. Leslie, *Endoscopy for unitary symmetric spaces*, arXiv:1910.09685, §3.
-/

public section

open Module

namespace TauCeti.FriedbergJacquet

variable {F K V₁ V₂ : Type*} [Field K] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂]
  [Module K V₂] {σ : K →+* K} {ε : ℤˣ}
  (H₁ : SignedHermitianSpace K V₁ σ ε) (H₂ : SignedHermitianSpace K V₂ σ ε)

/-! ### The symmetric representation -/

/-- The **symmetric representation** of the unitary Friedberg–Jacquet pair: the group
`U(W₁) × U(W₂)` acts on `Hom(W₂, W₁)` by `(g₁, g₂) • X = g₁ X g₂⁻¹`. It is Mathlib's
representation `Representation.linHom` on linear maps, for the tautological actions of the two
unitary groups through the two projections. -/
noncomputable def homRepresentation :
    Representation K (H₁.form.isometryGroup × H₂.form.isometryGroup) (V₂ →ₗ[K] V₁) :=
  Representation.linHom
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (H₂.form.isometryGroup.subtype.comp (MonoidHom.snd _ _)))
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (H₁.form.isometryGroup.subtype.comp (MonoidHom.fst _ _)))

/-- The symmetric representation acts by `(g₁, g₂) • X = g₁ X g₂⁻¹`. -/
@[simp]
theorem homRepresentation_apply (g : H₁.form.isometryGroup × H₂.form.isometryGroup)
    (X : V₂ →ₗ[K] V₁) :
    homRepresentation H₁ H₂ g X =
      (g.1 : V₁ ≃ₗ[K] V₁).toLinearMap ∘ₗ X ∘ₗ (g.2 : V₂ ≃ₗ[K] V₂).symm.toLinearMap :=
  LinearMap.ext fun _ ↦ by simp [homRepresentation, Representation.linHom_apply]

/-! ### The involution `θ` -/

variable (K V₁ V₂) in
/-- The involution `θ = Ad(1, -1)` of `End(W₁ × W₂)`: conjugation by `(v₁, v₂) ↦ (v₁, -v₂)`.
Away from characteristic `2` its fixed points are the block-diagonal endomorphisms and its
`(-1)`-eigenvectors the off-diagonal ones. -/
noncomputable def blockInvolution : Module.End K (V₁ × V₂) ≃ₗ[K] Module.End K (V₁ × V₂) :=
  ((LinearEquiv.refl K V₁).prodCongr (LinearEquiv.neg K)).conj

@[simp]
theorem blockInvolution_apply (T : Module.End K (V₁ × V₂)) (v : V₁ × V₂) :
    blockInvolution K V₁ V₂ T v = ((T (v.1, -v.2)).1, -(T (v.1, -v.2)).2) := by
  simp [blockInvolution, LinearEquiv.conj_apply]

/-- `θ` is an involution: `θ (θ T) = T`. -/
@[simp]
theorem blockInvolution_blockInvolution (T : Module.End K (V₁ × V₂)) :
    blockInvolution K V₁ V₂ (blockInvolution K V₁ V₂ T) = T :=
  LinearMap.ext fun v ↦ by simp

/-- `θ` is its own inverse. -/
@[simp]
theorem blockInvolution_symm : (blockInvolution K V₁ V₂).symm = blockInvolution K V₁ V₂ :=
  LinearEquiv.ext fun T ↦ by rw [LinearEquiv.symm_apply_eq, blockInvolution_blockInvolution]

variable [FiniteDimensional K V₂]

/-! ### The block embedding into the infinitesimal symmetric space -/

/-- The **off-diagonal block** `δ(X) = [[0, X], [-X^τ, 0]]` of `X : W₂ → W₁`: the endomorphism
`(v₁, v₂) ↦ (X v₂, -X^τ v₁)` of `W₁ × W₂`. -/
noncomputable def offDiagonalBlock (X : V₂ →ₗ[K] V₁) : Module.End K (V₁ × V₂) :=
  (X ∘ₗ LinearMap.snd K V₁ V₂).prod
    (-(signedHermitianHomAdjoint H₂ H₁ X ∘ₗ LinearMap.fst K V₁ V₂))

@[simp]
theorem offDiagonalBlock_apply (X : V₂ →ₗ[K] V₁) (v : V₁ × V₂) :
    offDiagonalBlock H₁ H₂ X v = (X v.2, -signedHermitianHomAdjoint H₂ H₁ X v.1) :=
  (rfl)

/-- The top-right block of `δ(X)` is `X`. -/
@[simp]
theorem fst_comp_offDiagonalBlock_comp_inr (X : V₂ →ₗ[K] V₁) :
    LinearMap.fst K V₁ V₂ ∘ₗ offDiagonalBlock H₁ H₂ X ∘ₗ LinearMap.inr K V₁ V₂ = X := by
  ext; simp

/-- `δ` is injective: `X` is the top-right block of `δ(X)`. -/
theorem offDiagonalBlock_injective : Function.Injective (offDiagonalBlock H₁ H₂) :=
  Function.LeftInverse.injective (g := fun T ↦ LinearMap.fst K V₁ V₂ ∘ₗ T ∘ₗ LinearMap.inr K V₁ V₂)
    (fst_comp_offDiagonalBlock_comp_inr H₁ H₂)

@[simp]
theorem offDiagonalBlock_zero : offDiagonalBlock H₁ H₂ 0 = 0 := by
  ext v <;> simp

@[simp]
theorem offDiagonalBlock_add (X Y : V₂ →ₗ[K] V₁) :
    offDiagonalBlock H₁ H₂ (X + Y) = offDiagonalBlock H₁ H₂ X + offDiagonalBlock H₁ H₂ Y := by
  ext v <;> simp [add_comm]

@[simp]
theorem offDiagonalBlock_neg (X : V₂ →ₗ[K] V₁) :
    offDiagonalBlock H₁ H₂ (-X) = -offDiagonalBlock H₁ H₂ X := by
  ext v <;> simp

/-- `δ(X)` lies in the `(-1)`-eigenspace of `θ`. -/
@[simp]
theorem blockInvolution_offDiagonalBlock (X : V₂ →ₗ[K] V₁) :
    blockInvolution K V₁ V₂ (offDiagonalBlock H₁ H₂ X) = -offDiagonalBlock H₁ H₂ X := by
  ext v <;> simp

/-! ### The signed contractions -/

/-- The **signed contraction** `r₁(X) = -X X^τ` of `X : W₂ → W₁`, an endomorphism of `W₁`. -/
noncomputable def leftContraction (X : V₂ →ₗ[K] V₁) : Module.End K V₁ :=
  -(X ∘ₗ signedHermitianHomAdjoint H₂ H₁ X)

/-- The **signed contraction** `r₂(X) = -X^τ X` of `X : W₂ → W₁`, an endomorphism of `W₂`. -/
noncomputable def rightContraction (X : V₂ →ₗ[K] V₁) : Module.End K V₂ :=
  -(signedHermitianHomAdjoint H₂ H₁ X ∘ₗ X)

theorem leftContraction_def (X : V₂ →ₗ[K] V₁) :
    leftContraction H₁ H₂ X = -(X ∘ₗ signedHermitianHomAdjoint H₂ H₁ X) :=
  (rfl)

theorem rightContraction_def (X : V₂ →ₗ[K] V₁) :
    rightContraction H₁ H₂ X = -(signedHermitianHomAdjoint H₂ H₁ X ∘ₗ X) :=
  (rfl)

@[simp]
theorem leftContraction_apply (X : V₂ →ₗ[K] V₁) (v : V₁) :
    leftContraction H₁ H₂ X v = -X (signedHermitianHomAdjoint H₂ H₁ X v) :=
  (rfl)

@[simp]
theorem rightContraction_apply (X : V₂ →ₗ[K] V₁) (v : V₂) :
    rightContraction H₁ H₂ X v = -signedHermitianHomAdjoint H₂ H₁ X (X v) :=
  (rfl)

@[simp]
theorem leftContraction_zero : leftContraction H₁ H₂ 0 = 0 := by
  simp [leftContraction_def]

@[simp]
theorem rightContraction_zero : rightContraction H₁ H₂ 0 = 0 := by
  simp [rightContraction_def]

/-! ### The adjoint and the block embedding as equivariant maps -/

/-- The adjoint transforms by `(g₁ X g₂⁻¹)^τ = g₂ X^τ g₁⁻¹`: taking adjoints intertwines the
symmetric representations on `Hom(W₂, W₁)` and on `Hom(W₁, W₂)`, the latter with the factors of
the group exchanged. -/
theorem signedHermitianHomAdjoint_homRepresentation
    (g : H₁.form.isometryGroup × H₂.form.isometryGroup) (X : V₂ →ₗ[K] V₁) :
    signedHermitianHomAdjoint H₂ H₁ (homRepresentation H₁ H₂ g X) =
      homRepresentation H₂ H₁ g.swap (signedHermitianHomAdjoint H₂ H₁ X) := by
  obtain ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := g
  refine signedHermitianHomAdjoint_unique H₂ H₁ fun v w ↦ ?_
  -- Move `g₁` to the right and `g₂` to the left; both are isometries.
  have h₁ := LinearMap.mem_isometryGroup_iff.1 hg₁ (X (g₂.symm v)) (g₁.symm w)
  have h₂ := LinearMap.mem_isometryGroup_iff.1 hg₂ (g₂.symm v)
    (signedHermitianHomAdjoint H₂ H₁ X (g₁.symm w))
  simp only [LinearEquiv.apply_symm_apply] at h₁ h₂
  simp [h₁, h₂]

variable [FiniteDimensional K V₁]

/-- `δ(X)` is skew-adjoint for the orthogonal sum `W₁ ⊥ W₂`: it lies in the Lie algebra `𝔲(W)`. -/
@[simp]
theorem signedHermitianAdjoint_offDiagonalBlock (X : V₂ →ₗ[K] V₁) :
    signedHermitianAdjoint (H₁.prod H₂) (offDiagonalBlock H₁ H₂ X) = -offDiagonalBlock H₁ H₂ X :=
  signedHermitianAdjoint_unique _ fun v w ↦ by simp [add_comm]

variable [CommSemiring F] [Algebra F K] [Module F V₁] [Module F V₂] [IsScalarTower F K V₁]
  [IsScalarTower F K V₂]

/-- The **infinitesimal symmetric space** of the pair `(U(W₁ ⊥ W₂), U(W₁) × U(W₂))`: the
`(-1)`-eigenspace of `θ = Ad(1, -1)` in the Lie algebra `𝔲(W₁ ⊥ W₂)` of skew-adjoint
endomorphisms. It is a module over any ring of scalars `F` fixed by the involution `σ`, such as the
base field of a quadratic extension; for nontrivial `σ` it is not stable under scalars from all
of `K`, since `(c T)* = σ c T*`. -/
def infinitesimalSymmetricSpace (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    Submodule F (Module.End K (V₁ × V₂)) where
  carrier := {T | signedHermitianAdjoint (H₁.prod H₂) T = -T ∧ blockInvolution K V₁ V₂ T = -T}
  add_mem' {S T} hS hT :=
    ⟨by rw [map_add, hS.1, hT.1, neg_add], by rw [map_add, hS.2, hT.2, neg_add]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c T hT := by
    refine ⟨?_, ?_⟩
    · simpa [hT.1] using
        signedHermitianHomAdjoint_smul_of_map_algebraMap (H₁.prod H₂) (H₁.prod H₂) (hσ c) T
    · rw [← algebraMap_smul K c T, map_smul, hT.2, smul_neg]

variable {H₁ H₂} in
/-- Membership in the infinitesimal symmetric space: `T* = -T` and `θ T = -T`. -/
theorem mem_infinitesimalSymmetricSpace_iff
    {hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c} {T : Module.End K (V₁ × V₂)} :
    T ∈ infinitesimalSymmetricSpace H₁ H₂ hσ ↔
      signedHermitianAdjoint (H₁.prod H₂) T = -T ∧ blockInvolution K V₁ V₂ T = -T :=
  Iff.rfl

/-- `δ(X)` lies in the infinitesimal symmetric space. -/
theorem offDiagonalBlock_mem_infinitesimalSymmetricSpace
    (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) (X : V₂ →ₗ[K] V₁) :
    offDiagonalBlock H₁ H₂ X ∈ infinitesimalSymmetricSpace H₁ H₂ hσ :=
  ⟨signedHermitianAdjoint_offDiagonalBlock H₁ H₂ X, blockInvolution_offDiagonalBlock H₁ H₂ X⟩

/-- Away from characteristic `2`, every element `T` of the infinitesimal symmetric space is the
off-diagonal block of its top-right block. -/
theorem offDiagonalBlock_fst_comp_comp_inr (h2 : (2 : K) ≠ 0)
    {hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c} {T : Module.End K (V₁ × V₂)}
    (hT : T ∈ infinitesimalSymmetricSpace H₁ H₂ hσ) :
    offDiagonalBlock H₁ H₂ (LinearMap.fst K V₁ V₂ ∘ₗ T ∘ₗ LinearMap.inr K V₁ V₂) = T := by
  -- `θ T = -T` kills the diagonal blocks of `T`.
  have hθ (v : V₁ × V₂) : (T (v.1, -v.2)).1 = -(T v).1 ∧ (T (v.1, -v.2)).2 = (T v).2 := by
    have h := LinearMap.congr_fun hT.2 v
    simp only [blockInvolution_apply, LinearMap.neg_apply] at h
    exact ⟨congrArg Prod.fst h, neg_inj.1 (congrArg Prod.snd h)⟩
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have h₁ (v : V₁) : (T (v, 0)).1 = 0 :=
    eq_zero_of_eq_neg_of_invertible_two (R := K) (by simpa using (hθ (v, 0)).1)
  have h₂ (v : V₂) : (T (0, v)).2 = 0 := by
    have h := (hθ (0, v)).2
    rw [show ((0 : V₁), -v) = -((0 : V₁), v) by simp, map_neg] at h
    exact eq_zero_of_eq_neg_of_invertible_two (R := K) (by simpa using h.symm)
  -- `T* = -T` identifies the lower-left block with minus the adjoint of the upper-right one.
  have hadj : signedHermitianHomAdjoint H₂ H₁
      (LinearMap.fst K V₁ V₂ ∘ₗ T ∘ₗ LinearMap.inr K V₁ V₂) =
        -(LinearMap.snd K V₁ V₂ ∘ₗ T ∘ₗ LinearMap.inl K V₁ V₂) := by
    refine signedHermitianHomAdjoint_unique H₂ H₁ fun v w ↦ ?_
    have h := signedHermitianAdjoint_form_right (H₁.prod H₂) T (0, v) (w, 0)
    rw [hT.1] at h
    simpa [h₂] using h.symm
  refine LinearMap.ext fun v ↦ ?_
  have hv : T v = T (v.1, 0) + T (0, v.2) := by rw [← map_add]; simp
  rw [offDiagonalBlock_apply, hadj, hv]
  ext <;> simp [h₁, h₂]

omit [FiniteDimensional K V₁] in
/-- The off-diagonal block is linear over any ring of scalars `F` fixed by `σ`. -/
theorem offDiagonalBlock_smul (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) (c : F)
    (X : V₂ →ₗ[K] V₁) : offDiagonalBlock H₁ H₂ (c • X) = c • offDiagonalBlock H₁ H₂ X := by
  ext v <;> simp [signedHermitianHomAdjoint_smul_of_map_algebraMap _ _ (hσ c)]

/-- Away from characteristic `2`, the off-diagonal block `X ↦ δ(X)` is an `F`-linear isomorphism
from `Hom(W₂, W₁)` onto the infinitesimal symmetric space, for any ring of scalars `F` fixed by
`σ`; its inverse takes the top-right block. -/
noncomputable def homEquivInfinitesimalSymmetricSpace (h2 : (2 : K) ≠ 0)
    (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) :
    (V₂ →ₗ[K] V₁) ≃ₗ[F] infinitesimalSymmetricSpace H₁ H₂ hσ where
  toFun X := ⟨offDiagonalBlock H₁ H₂ X, offDiagonalBlock_mem_infinitesimalSymmetricSpace H₁ H₂ hσ X⟩
  invFun T := LinearMap.fst K V₁ V₂ ∘ₗ (T : Module.End K (V₁ × V₂)) ∘ₗ LinearMap.inr K V₁ V₂
  map_add' X Y := Subtype.ext <| offDiagonalBlock_add H₁ H₂ X Y
  map_smul' c X := Subtype.ext <| offDiagonalBlock_smul H₁ H₂ hσ c X
  left_inv X := fst_comp_offDiagonalBlock_comp_inr H₁ H₂ X
  right_inv T := Subtype.ext <| offDiagonalBlock_fst_comp_comp_inr H₁ H₂ h2 T.property

@[simp]
theorem coe_homEquivInfinitesimalSymmetricSpace_apply (h2 : (2 : K) ≠ 0)
    (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c) (X : V₂ →ₗ[K] V₁) :
    (homEquivInfinitesimalSymmetricSpace H₁ H₂ h2 hσ X : Module.End K (V₁ × V₂)) =
      offDiagonalBlock H₁ H₂ X :=
  (rfl)

@[simp]
theorem homEquivInfinitesimalSymmetricSpace_symm_apply (h2 : (2 : K) ≠ 0)
    (hσ : ∀ c : F, σ (algebraMap F K c) = algebraMap F K c)
    (T : infinitesimalSymmetricSpace H₁ H₂ hσ) :
    (homEquivInfinitesimalSymmetricSpace H₁ H₂ h2 hσ).symm T =
      LinearMap.fst K V₁ V₂ ∘ₗ (T : Module.End K (V₁ × V₂)) ∘ₗ LinearMap.inr K V₁ V₂ :=
  (rfl)

omit [FiniteDimensional K V₁] in
/-- The block embedding intertwines the symmetric representation with conjugation by
`diag(g₁, g₂)`: `δ(g₁ X g₂⁻¹) = diag(g₁, g₂) δ(X) diag(g₁, g₂)⁻¹`. -/
theorem offDiagonalBlock_homRepresentation (g : H₁.form.isometryGroup × H₂.form.isometryGroup)
    (X : V₂ →ₗ[K] V₁) :
    offDiagonalBlock H₁ H₂ (homRepresentation H₁ H₂ g X) =
      ((g.1 : V₁ ≃ₗ[K] V₁).prodCongr (g.2 : V₂ ≃ₗ[K] V₂)).conj (offDiagonalBlock H₁ H₂ X) := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [offDiagonalBlock_apply, signedHermitianHomAdjoint_homRepresentation]
  simp [LinearEquiv.conj_apply]

/-! ### Properties of the signed contractions -/

/-- Exchanging `W₁` and `W₂`, the second contraction is the first one of the adjoint:
`r₂(X) = r₁(X^τ)`. -/
theorem rightContraction_eq_leftContraction (X : V₂ →ₗ[K] V₁) :
    rightContraction H₁ H₂ X = leftContraction H₂ H₁ (signedHermitianHomAdjoint H₂ H₁ X) := by
  simp [leftContraction_def, rightContraction_def]

/-- The first contraction is self-adjoint: `r₁(X)` lies in `Herm(W₁)`. -/
@[simp]
theorem signedHermitianAdjoint_leftContraction (X : V₂ →ₗ[K] V₁) :
    signedHermitianAdjoint H₁ (leftContraction H₁ H₂ X) = leftContraction H₁ H₂ X := by
  rw [← signedHermitianHomAdjoint_self, leftContraction_def, map_neg,
    signedHermitianHomAdjoint_comp H₁ H₂ H₁, signedHermitianHomAdjoint_signedHermitianHomAdjoint]

/-- The second contraction is self-adjoint: `r₂(X)` lies in `Herm(W₂)`. -/
@[simp]
theorem signedHermitianAdjoint_rightContraction (X : V₂ →ₗ[K] V₁) :
    signedHermitianAdjoint H₂ (rightContraction H₁ H₂ X) = rightContraction H₁ H₂ X := by
  rw [rightContraction_eq_leftContraction, signedHermitianAdjoint_leftContraction]

omit [FiniteDimensional K V₁] in
/-- The first contraction is `U(W₁)`-equivariant and `U(W₂)`-invariant:
`r₁(g₁ X g₂⁻¹) = g₁ r₁(X) g₁⁻¹`. -/
theorem leftContraction_homRepresentation (g : H₁.form.isometryGroup × H₂.form.isometryGroup)
    (X : V₂ →ₗ[K] V₁) :
    leftContraction H₁ H₂ (homRepresentation H₁ H₂ g X) =
      (g.1 : V₁ ≃ₗ[K] V₁).conj (leftContraction H₁ H₂ X) := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [leftContraction_apply, signedHermitianHomAdjoint_homRepresentation]
  simp [LinearEquiv.conj_apply]

omit [FiniteDimensional K V₁] in
/-- The second contraction is `U(W₂)`-equivariant and `U(W₁)`-invariant:
`r₂(g₁ X g₂⁻¹) = g₂ r₂(X) g₂⁻¹`. -/
theorem rightContraction_homRepresentation (g : H₁.form.isometryGroup × H₂.form.isometryGroup)
    (X : V₂ →ₗ[K] V₁) :
    rightContraction H₁ H₂ (homRepresentation H₁ H₂ g X) =
      (g.2 : V₂ ≃ₗ[K] V₂).conj (rightContraction H₁ H₂ X) := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [rightContraction_apply, signedHermitianHomAdjoint_homRepresentation]
  simp [LinearEquiv.conj_apply]

/-- The characteristic polynomials of the two contractions `r₁(X) = -X X^τ` and `r₂(X) = -X^τ X`
agree up to a power of `X` accounting for the dimensions of `W₁` and `W₂`:
`X ^ dim W₂ * charpoly r₁(X) = X ^ dim W₁ * charpoly r₂(X)`. -/
theorem X_pow_finrank_mul_charpoly_leftContraction_eq_X_pow_finrank_mul_charpoly_rightContraction
    (X : V₂ →ₗ[K] V₁) :
    Polynomial.X ^ finrank K V₂ * (leftContraction H₁ H₂ X).charpoly =
      Polynomial.X ^ finrank K V₁ * (rightContraction H₁ H₂ X).charpoly := by
  rw [leftContraction_def, rightContraction_def, ← LinearMap.neg_comp, ← LinearMap.comp_neg]
  exact LinearMap.X_pow_finrank_mul_charpoly_comp_comm _ _

/-- When `W₁` and `W₂` have the same dimension, the two contractions `r₁(X) = -X X^τ` and
`r₂(X) = -X^τ X` have the same characteristic polynomial. -/
theorem charpoly_leftContraction_eq_charpoly_rightContraction (h : finrank K V₁ = finrank K V₂)
    (X : V₂ →ₗ[K] V₁) :
    (leftContraction H₁ H₂ X).charpoly = (rightContraction H₁ H₂ X).charpoly := by
  rw [leftContraction_def, rightContraction_def, ← LinearMap.neg_comp, ← LinearMap.comp_neg]
  exact LinearMap.charpoly_comp_comm _ _ h

/-- Between standard hermitian spaces the first contraction of a matrix `A` is `-A Aᴴ`, where
`Aᴴ` is the transpose of `A` with `σ` applied to each entry. -/
theorem leftContraction_standard_toLin' [RingHomInvPair σ σ] {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (A : Matrix m n K) :
    leftContraction (SignedHermitianSpace.standard σ m) (SignedHermitianSpace.standard σ n)
        (Matrix.toLin' A) = Matrix.toLin' (-(A * (A.map σ).transpose)) := by
  rw [leftContraction_def, signedHermitianHomAdjoint_standard_toLin', ← Matrix.toLin'_mul,
    map_neg]

/-- Between standard hermitian spaces the second contraction of a matrix `A` is `-Aᴴ A`, where
`Aᴴ` is the transpose of `A` with `σ` applied to each entry. -/
theorem rightContraction_standard_toLin' [RingHomInvPair σ σ] {m n : Type*} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (A : Matrix m n K) :
    rightContraction (SignedHermitianSpace.standard σ m) (SignedHermitianSpace.standard σ n)
        (Matrix.toLin' A) = Matrix.toLin' (-((A.map σ).transpose * A)) := by
  rw [rightContraction_def, signedHermitianHomAdjoint_standard_toLin', ← Matrix.toLin'_mul,
    map_neg]

end TauCeti.FriedbergJacquet
