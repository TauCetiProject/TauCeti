/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Product
public import TauCeti.Topology.Algebra.PointTopology.Functoriality

/-!
# Cartan involutions of real affine algebraic groups

Let `H` be an affine group scheme over `ℝ`, given by its commutative coordinate Hopf algebra, so
that its complex points are the `ℝ`-algebra homomorphisms `H →ₐ[ℝ] ℂ`. Complex conjugation acts on
them by `g ↦ conj g`, postcomposition with `star`. An involution `θ` of `H`, that is a
coordinate Hopf-algebra automorphism with `θ ∘ θ = 1`, twists this action to `g ↦ θ(conj g)`.
Its fixed points

```text
H^(θ)(ℝ) = {g ∈ H(ℂ) : g = θ(conj g)}
```

are the real points of the real form `H^(θ)` of `H` defined by `θ`. The involution `θ` is a
**Cartan involution** when `H^(θ)(ℝ)` is compact, in the topology of the complex points. That
topology is the point topology, induced from the product topology on `H → ℂ`; when `H` is of finite
type it is the usual topology on the complex points of an affine variety.

For the identity involution the twisted real form is `H` itself, so the identity is a Cartan
involution exactly when the real points of `H` are compact (`TauCeti.isCartanInvolution_refl_iff`).
For `GLₙ` the standard example is inverse transpose, whose twisted real form is the unitary group
(`TauCeti.GeneralLinear.isCartanInvolution_inverseTransposeCoordinateIso`).

For real affine group schemes `G₁ = Spec H₁` and `G₂ = Spec H₂`, the coordinate Hopf algebra of
`G₁ × G₂` is `H₁ ⊗[ℝ] H₂`, and automorphisms `θ₁`, `θ₂` of the factors give the product
automorphism `θ₁ × θ₂`, represented by `CommHopfAlgCat.tensorProductCongr θ₁ θ₂`. Its twisted
real form is the product of the twisted real forms of `θ₁` and `θ₂`
(`TauCeti.twistedRealPoints_tensorProductCongr`), and these always contain the identity point.
Hence `θ₁ × θ₂` is a Cartan involution exactly when `θ₁` and `θ₂` are
(`TauCeti.isCartanInvolution_tensorProductCongr_iff`).

## Main definitions

* `TauCeti.twistedRealPoints`: the complex points `g` of `H` with `g = θ(conj g)`.
* `TauCeti.IsCartanInvolution`: `θ` is an involution whose twisted real points are compact.

## Main results

* `TauCeti.mem_twistedRealPoints_iff_comp_eq`: a complex point is twisted-real exactly when
  precomposing it with `θ` is the same as postcomposing it with complex conjugation.
* `TauCeti.isCartanInvolution_iff_isCompact`: the compactness condition, read in the point
  topology on the complex points.
* `TauCeti.isCartanInvolution_refl_iff`: the identity is a Cartan involution exactly when the real
  points are compact.
* `TauCeti.one_mem_twistedRealPoints`: the identity point is twisted-real for every automorphism.
* `TauCeti.twistedRealPoints_tensorProductCongr`: the twisted real points of a product automorphism
  are the pairs of twisted real points of the factors.
* `TauCeti.isCartanInvolution_tensorProductCongr_iff`: a product automorphism `θ₁ × θ₂` is a
  Cartan involution exactly when `θ₁` and `θ₂` are.

## References

* J. S. Milne, *Introduction to Shimura varieties*, notes, version of 16 September 2017, §1,
  definition (9) and Example 1.17(a), p. 15.
-/

public section

open CategoryTheory Topology

namespace TauCeti

universe v

variable {H : CommHopfAlgCat.{v} ℝ}

/-- **The twisted real points of an automorphism `θ` of a real affine group scheme**: the complex
points `p` with `p = θ(conj p)`, where `conj p` is the complex conjugate of `p`. The point
`θ(conj p)` is `h ↦ star (p (θ h))`, so `p = θ(conj p)` is the condition
`p h = star (p (θ h))` for all `h`. When `θ` is an involution these are the real points of the
real form of `H` twisted by `θ`. -/
def twistedRealPoints (θ : H ≅ H) : Set (H →ₐ[ℝ] ℂ) :=
  {p | ∀ h : H, p h = star (p (θ.hom.hom h))}

/-- A complex point `p` is twisted-real exactly when `p h = star (p (θ h))` for every `h`. -/
@[simp]
theorem mem_twistedRealPoints_iff {θ : H ≅ H} {p : H →ₐ[ℝ] ℂ} :
    p ∈ twistedRealPoints θ ↔ ∀ h : H, p h = star (p (θ.hom.hom h)) :=
  Iff.rfl

/-- A complex point is twisted-real exactly when precomposing it with `θ` is the same as
postcomposing it with complex conjugation: this is `p = θ(conj p)` with complex conjugation applied
to both sides. -/
theorem mem_twistedRealPoints_iff_comp_eq {θ : H ≅ H} {p : H →ₐ[ℝ] ℂ} :
    p ∈ twistedRealPoints θ ↔
      p.comp (θ.hom.hom : H →ₐ[ℝ] H) = (Complex.conjAe : ℂ →ₐ[ℝ] ℂ).comp p := by
  simp only [mem_twistedRealPoints_iff, AlgHom.ext_iff, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    Complex.conjAe_coe, starRingEnd_apply]
  exact forall_congr' fun _ ↦ eq_star_iff_eq_star

/-- **Cartan involutions of a real affine algebraic group** (Milne, *Introduction to Shimura
varieties*, §1, definition (9)). An automorphism `θ` of the coordinate Hopf algebra is a Cartan
involution when it is an involution and its twisted real points `{g : g = θ(conj g)}` form a
compact subset of the complex points, with the topology induced from the product topology on
`H → ℂ`. -/
structure IsCartanInvolution (θ : H ≅ H) : Prop where
  /-- A Cartan involution is an involution. -/
  hom_comp_self : θ.hom ≫ θ.hom = 𝟙 H
  /-- The twisted real points of a Cartan involution are compact. -/
  isCompact : IsCompact ((fun p : H →ₐ[ℝ] ℂ ↦ (p : H → ℂ)) '' twistedRealPoints θ)

open scoped PointTopology in
/-- The compactness condition of a Cartan involution, read in the point topology on the complex
points. -/
theorem isCartanInvolution_iff_isCompact {θ : H ≅ H} :
    IsCartanInvolution θ ↔ θ.hom ≫ θ.hom = 𝟙 H ∧ IsCompact (twistedRealPoints θ) := by
  rw [PointTopology.isEmbedding_coeFn.isCompact_iff]
  exact ⟨fun h ↦ ⟨h.hom_comp_self, h.isCompact⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- **The twisted real points of the identity are the real points**, embedded in the complex
points. -/
theorem twistedRealPoints_refl :
    twistedRealPoints (Iso.refl H) = Set.range fun q : H →ₐ[ℝ] ℝ ↦ (Algebra.ofId ℝ ℂ).comp q := by
  ext p
  simp only [mem_twistedRealPoints_iff, Iso.refl_hom, Set.mem_range]
  constructor
  · intro hp
    -- A complex point with real values is the real point `h ↦ (p h).re`.
    have hre (h : H) : ((p h).re : ℂ) = p h := Complex.conj_eq_iff_re.mp (hp h).symm
    refine ⟨{ toFun h := (p h).re
              map_one' := by simp
              map_mul' x y := by
                rw [← Complex.ofReal_inj, Complex.ofReal_mul, hre, hre, hre, map_mul]
              map_zero' := by simp
              map_add' x y := by simp
              commutes' r := by simp }, ?_⟩
    ext h
    exact hre h
  · rintro ⟨q, rfl⟩ h
    simp

/-- **The identity is a Cartan involution exactly when the real points are compact**, in the
topology induced from the product topology on `H → ℝ`. -/
theorem isCartanInvolution_refl_iff :
    IsCartanInvolution (Iso.refl H) ↔
      IsCompact (Set.range fun q : H →ₐ[ℝ] ℝ ↦ (q : H → ℝ)) := by
  have hemb : IsEmbedding fun f : H → ℝ ↦ fun h ↦ (f h : ℂ) :=
    IsEmbedding.piMap fun _ ↦ Complex.isometry_ofReal.isEmbedding
  have himage : ((fun p : H →ₐ[ℝ] ℂ ↦ (p : H → ℂ)) '' twistedRealPoints (Iso.refl H)) =
      (fun f : H → ℝ ↦ fun h ↦ (f h : ℂ)) '' Set.range fun q : H →ₐ[ℝ] ℝ ↦ (q : H → ℝ) := by
    rw [twistedRealPoints_refl, ← Set.range_comp, ← Set.range_comp]
    simp only [Function.comp_def, AlgHom.coe_comp, Algebra.ofId_apply, Complex.coe_algebraMap]
  rw [hemb.isCompact_iff, ← himage]
  exact ⟨IsCartanInvolution.isCompact, fun h ↦ ⟨by simp, h⟩⟩

section Product

open TensorProduct

/-- **The identity point is twisted-real for every automorphism**: an automorphism `θ` of the
coordinate Hopf algebra preserves the counit, and the identity point `h ↦ ε(h)` takes real values,
so it satisfies `1 = θ(conj 1)`. -/
theorem one_mem_twistedRealPoints (θ : H ≅ H) :
    (1 : WithConv (H →ₐ[ℝ] ℂ)).ofConv ∈ twistedRealPoints θ := by
  intro h
  simp [AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply]

/-- The twisted real points of an automorphism are nonempty: they contain the identity point. -/
theorem twistedRealPoints_nonempty (θ : H ≅ H) : (twistedRealPoints θ).Nonempty :=
  ⟨_, one_mem_twistedRealPoints θ⟩

variable {H₁ H₂ : CommHopfAlgCat.{v} ℝ}

/-- **Twisted real points of a product.** A complex point of `H₁ ⊗[ℝ] H₂`, that is a complex
point of the product group, is twisted-real for the product automorphism `θ₁ ⊗ θ₂` exactly when
its restrictions to the two factors are twisted-real for `θ₁` and for `θ₂`. -/
theorem mem_twistedRealPoints_tensorProductCongr_iff {θ₁ : H₁ ≅ H₁} {θ₂ : H₂ ≅ H₂}
    {p : H₁ ⊗[ℝ] H₂ →ₐ[ℝ] ℂ} :
    p ∈ twistedRealPoints (CommHopfAlgCat.tensorProductCongr θ₁ θ₂) ↔
      p.comp Algebra.TensorProduct.includeLeft ∈ twistedRealPoints θ₁ ∧
        p.comp Algebra.TensorProduct.includeRight ∈ twistedRealPoints θ₂ := by
  simp only [mem_twistedRealPoints_iff, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]
  refine ⟨fun hp ↦ ⟨fun x ↦ by simpa using hp (x ⊗ₜ 1), fun y ↦ by simpa using hp (1 ⊗ₜ y)⟩,
    fun ⟨hp₁, hp₂⟩ t ↦ ?_⟩
  -- A point of the tensor product is the product of its restrictions to the two factors.
  have hsplit (x : H₁) (y : H₂) : p (x ⊗ₜ y) = p (x ⊗ₜ 1) * p (1 ⊗ₜ y) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [CommHopfAlgCat.tensorProductCongr_hom_hom_tmul, hsplit (θ₁.hom.hom x), star_mul', ← hp₁,
      ← hp₂, hsplit]
  | add t u ht hu => simp only [map_add, ht, hu, star_add]

open scoped PointTopology in
/-- Under the identification of the complex points of `H₁ ⊗[ℝ] H₂` with pairs of complex points
(`TauCeti.PointTopology.tensorProductHomeomorph`), the twisted real points of `θ₁ ⊗ θ₂` are the
pairs of twisted real points of `θ₁` and `θ₂`. -/
theorem twistedRealPoints_tensorProductCongr (θ₁ : H₁ ≅ H₁) (θ₂ : H₂ ≅ H₂) :
    twistedRealPoints (CommHopfAlgCat.tensorProductCongr θ₁ θ₂) =
      PointTopology.tensorProductHomeomorph ℝ H₁ H₂ ℂ ⁻¹'
        (twistedRealPoints θ₁ ×ˢ twistedRealPoints θ₂) := by
  ext p
  have h₁ : (PointTopology.tensorProductHomeomorph ℝ H₁ H₂ ℂ p).1 =
      p.comp Algebra.TensorProduct.includeLeft :=
    AlgHom.ext fun _ ↦ PointTopology.tensorProductHomeomorph_apply_fst _ _
  have h₂ : (PointTopology.tensorProductHomeomorph ℝ H₁ H₂ ℂ p).2 =
      p.comp Algebra.TensorProduct.includeRight :=
    AlgHom.ext fun _ ↦ PointTopology.tensorProductHomeomorph_apply_snd _ _
  rw [Set.mem_preimage, Set.mem_prod, h₁, h₂, mem_twistedRealPoints_tensorProductCongr_iff]

open scoped PointTopology in
/-- **Cartan involutions of a product**: for real affine group schemes `G₁ = Spec H₁` and
`G₂ = Spec H₂`, the product automorphism `θ₁ × θ₂` of `G₁ × G₂` is a Cartan involution exactly
when `θ₁` and `θ₂` are. The twisted real form of `θ₁ × θ₂` is the product of the twisted real
forms, which is compact exactly when both factors are, since neither factor is empty. -/
theorem isCartanInvolution_tensorProductCongr_iff {θ₁ : H₁ ≅ H₁} {θ₂ : H₂ ≅ H₂} :
    IsCartanInvolution (CommHopfAlgCat.tensorProductCongr θ₁ θ₂) ↔
      IsCartanInvolution θ₁ ∧ IsCartanInvolution θ₂ := by
  simp only [isCartanInvolution_iff_isCompact, twistedRealPoints_tensorProductCongr,
    Homeomorph.isCompact_preimage, CommHopfAlgCat.tensorProductCongr_hom_comp_self_iff]
  refine ⟨fun ⟨⟨h₁, h₂⟩, hc⟩ ↦ ⟨⟨h₁, ?_⟩, ⟨h₂, ?_⟩⟩, fun ⟨⟨h₁, hc₁⟩, ⟨h₂, hc₂⟩⟩ ↦
    ⟨⟨h₁, h₂⟩, hc₁.prod hc₂⟩⟩
  · simpa only [Set.fst_image_prod _ (twistedRealPoints_nonempty θ₂)] using
      hc.image continuous_fst
  · simpa only [Set.snd_image_prod (twistedRealPoints_nonempty θ₁)] using
      hc.image continuous_snd

/-- The product of two Cartan involutions is a Cartan involution of the product. -/
theorem IsCartanInvolution.tensorProductCongr {θ₁ : H₁ ≅ H₁} {θ₂ : H₂ ≅ H₂}
    (h₁ : IsCartanInvolution θ₁) (h₂ : IsCartanInvolution θ₂) :
    IsCartanInvolution (CommHopfAlgCat.tensorProductCongr θ₁ θ₂) :=
  isCartanInvolution_tensorProductCongr_iff.2 ⟨h₁, h₂⟩

end Product

end TauCeti
