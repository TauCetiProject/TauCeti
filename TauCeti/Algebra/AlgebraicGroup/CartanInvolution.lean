/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Topology.Algebra.PointTopology.Basic

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

end TauCeti
