/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Unitary
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.GeneralLinearGroup
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# The finite adelic unitary group at a split place

Let `E` be a CM field with finite adeles `𝔸_f`, and `G_f = U(1_n)(𝔸_f)` its finite adelic unitary
group (`TauCeti.finiteAdelicUnitaryGroup`). A finite place `w` of `E` is **split** when its
conjugate place `conj w` (`IsDedekindDomain.HeightOneSpectrum.conjPlace`) is different from `w`,
that is when the place of the maximal totally real subfield below `w` splits in `E`. The
components of `g ∈ G_f` at `w` and `conj w` determine each other
(`TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace`), and at a split place the component at `w`
alone is unconstrained: this file constructs the homomorphism

`ι_w : GL_n(E_w) → G_f`,

whose value at `g` has component `g` at `w`, the inverse transpose `(σ(g)⁻¹)ᵀ` of the conjugate
`σ(g)` of `g` at `conj w` (`σ : E_w ≃ E_{conj w}` the isomorphism extending the conjugation of `E`),
and `1` at every other place. With `y ∈ GL_n(𝔸_f)` the element with component `g` at `w` and `1`
elsewhere (`IsDedekindDomain.FiniteAdeleRing.ofAdicCompletionGL`), it is `ι_w(g) = y (y*)⁻¹`: the
adjoint `y*` is trivial away from `conj w`, so it commutes with `y`, and `y (y*)⁻¹` is then unitary
(`MonoidHom.mulStarInv`).

The Hecke operators of a representation of `G_f` at a split place `w` are those of `GL_n(E_w)`,
acting through `ι_w` on the vectors fixed by `ι_w(GL_n(𝒪_w))`; this is how spherical vectors and
Hecke eigenforms on unitary groups are read at split places.

## Main definitions

* `TauCeti.finiteAdelicUnitaryGroup.ofSplitPlace E ι w hw`: the homomorphism
  `ι_w : GL_n(E_w) → G_f` at a split place `w` (`hw : conj w ≠ w`).

## Main results

* `IsDedekindDomain.FiniteAdeleRing.map_proj_conjPlace_star_inv`: for `x ∈ GL_n(𝔸_f)`, the
  component of `(x*)⁻¹` at `conj w` is the inverse transpose of the conjugate of `x_w`.
* `IsDedekindDomain.FiniteAdeleRing.commute_ofAdicCompletionGL_star`: at a split place `w`, an
  element of `GL_n(𝔸_f)` trivial away from `w` commutes with the adjoint of any other such element.
* `TauCeti.finiteAdelicUnitaryGroup.proj_eq_map`: the component of `g ∈ G_f` at `w` is the
  component of `g` read in `GL_n(𝔸_f)`.
* `TauCeti.finiteAdelicUnitaryGroup.proj_ofSplitPlace_self`,
  `TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace_ofSplitPlace`,
  `TauCeti.finiteAdelicUnitaryGroup.proj_ofSplitPlace_of_ne`: the components of `ι_w(g)`.
* `TauCeti.finiteAdelicUnitaryGroup.ofSplitPlace_injective`,
  `TauCeti.finiteAdelicUnitaryGroup.continuous_ofSplitPlace`: `ι_w` is injective and continuous.
* `TauCeti.finiteAdelicUnitaryGroup.range_ofSplitPlace`: the image of `ι_w` is the set of
  elements of `G_f` supported on `{w, conj w}`, that is with component `1` at every other place.
* `TauCeti.finiteAdelicUnitaryGroup.ofSplitPlace_mem_integralAdelicUnitaryGroup_iff`:
  `ι_w(g) ∈ K₀` exactly when `g ∈ GL_n(𝒪_w)`.

## References

* B. H. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61–93.

## Attribution

The homomorphism `ι_w` and the statements on its components, its image and its integral points
are those of `New.ofSplitPlace`, `New.range_ofSplitPlace` and `New.ofSplitPlace_mem_stdLevel` in
the files `src/Lib/Adelic/Unitary/Defs.lean` and
`src/Lib/Adelic/Unitary/ComponentsAndBlockSums.lean` of grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC); the
formalization here, through the factorisation `ι_w(g) = y (y*)⁻¹`, is independent of that code.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing Matrix
  NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

namespace IsDedekindDomain.FiniteAdeleRing

/-- **The adjoint of an adelic matrix at a conjugate place.** For `x ∈ GL_n(𝔸_f)` and a finite
place `w`, the component at `conj w` of the inverse of the adjoint `x* = (conj x)ᵀ` is the inverse
transpose of the image of `x_w` under the isomorphism `σ : E_w ≃ E_{conj w}` extending the
conjugation of `E`: `((x*)⁻¹)_{conj w} = (σ(x_w)⁻¹)ᵀ`. For `x ∈ G_f`, where `(x*)⁻¹ = x`, this is
`TauCeti.finiteAdelicUnitaryGroup.proj_conjPlace`. -/
theorem map_proj_conjPlace_star_inv (x : GL ι 𝔸ᶠ[E]) (w : HeightOneSpectrum (𝓞 E)) :
    GeneralLinearGroup.map (proj E w.conjPlace : _ →+* w.conjPlace.adicCompletion E) (star x)⁻¹ =
      GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map
        (adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w) :
          w.adicCompletion E →+* w.conjPlace.adicCompletion E)
        (GeneralLinearGroup.map (proj E w : _ →+* w.adicCompletion E) x)) := by
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  rw [← star_inv, GeneralLinearGroup.coe_inverseTranspose, transpose_apply, ← map_inv, ← map_inv]
  simp only [GeneralLinearGroup.map_apply, RingHom.coe_coe, proj_apply, Units.coe_star, star_apply]
  exact star_apply_conjPlace _ w

/-- The adjoint of the element of `GL_n(𝔸_f)` with component `g` at `w` and `1` elsewhere is `1`
away from `conj w`. -/
theorem map_proj_star_ofAdicCompletionGL_of_ne {u w : HeightOneSpectrum (𝓞 E)}
    (h : u ≠ w.conjPlace) (g : GL ι (w.adicCompletion E)) :
    GeneralLinearGroup.map (FiniteAdeleRing.proj E u : _ →+* u.adicCompletion E)
      (star (ofAdicCompletionGL E w g)) = 1 := by
  obtain ⟨v, rfl⟩ : ∃ v, u = v.conjPlace := ⟨u.conjPlace, (conjPlace_conjPlace u).symm⟩
  have hv : v ≠ w := fun hvw ↦ h (hvw ▸ rfl)
  rw [← _root_.inv_inj, ← map_inv, map_proj_conjPlace_star_inv,
    map_proj_ofAdicCompletionGL_of_ne hv, map_one, map_one, inv_one]

/-- At a split place `w`, the element of `GL_n(𝔸_f)` with component `a` at `w` and `1` elsewhere
commutes with the adjoint of the element with component `b` at `w` and `1` elsewhere, which is
trivial away from `conj w ≠ w`. -/
theorem commute_ofAdicCompletionGL_star {w : HeightOneSpectrum (𝓞 E)} (hw : w.conjPlace ≠ w)
    (a b : GL ι (w.adicCompletion E)) :
    Commute (ofAdicCompletionGL E w a) (star (ofAdicCompletionGL E w b)) :=
  commute_of_forall_map_proj_eq_one_or fun u ↦ by
    rcases eq_or_ne u w with rfl | hu
    · exact Or.inr (map_proj_star_ofAdicCompletionGL_of_ne hw.symm b)
    · exact Or.inl (map_proj_ofAdicCompletionGL_of_ne hu a)

end IsDedekindDomain.FiniteAdeleRing

namespace TauCeti

namespace finiteAdelicUnitaryGroup

/-- The component of `g ∈ G_f` at a finite place `w` is the component of `g` read in
`GL_n(𝔸_f)`. -/
theorem proj_eq_map (w : HeightOneSpectrum (𝓞 E)) (g : finiteAdelicUnitaryGroup E ι) :
    proj E ι w g = GeneralLinearGroup.map (FiniteAdeleRing.proj E w : _ →+* w.adicCompletion E)
      (g : GL ι 𝔸ᶠ[E]) :=
  GeneralLinearGroup.ext fun i j ↦ by
    simp only [proj_apply, GeneralLinearGroup.map_apply, RingHom.coe_coe,
      FiniteAdeleRing.proj_apply]

variable (E ι) in
/-- The **embedding `ι_w : GL_n(E_w) → G_f` at a split place** `w` (`conj w ≠ w`): `ι_w(g)` has
component `g` at `w`, the inverse transpose of the conjugate of `g` at `conj w`
(`proj_conjPlace_ofSplitPlace`), and `1` at every other place. It is `y (y*)⁻¹` for the element
`y = ofAdicCompletionGL E w g` of `GL_n(𝔸_f)` with component `g` at `w` and `1` elsewhere
(`coe_ofSplitPlace`). -/
def ofSplitPlace (w : HeightOneSpectrum (𝓞 E)) (hw : w.conjPlace ≠ w) :
    GL ι (w.adicCompletion E) →* finiteAdelicUnitaryGroup E ι :=
  (ofAdicCompletionGL E w).mulStarInv (commute_ofAdicCompletionGL_star hw)

variable {w : HeightOneSpectrum (𝓞 E)} (hw : w.conjPlace ≠ w)

/-- `ι_w(g) = y (y*)⁻¹` for the element `y` of `GL_n(𝔸_f)` with component `g` at `w` and `1`
elsewhere. -/
theorem coe_ofSplitPlace (g : GL ι (w.adicCompletion E)) :
    (ofSplitPlace E ι w hw g : GL ι 𝔸ᶠ[E]) =
      ofAdicCompletionGL E w g * (star (ofAdicCompletionGL E w g))⁻¹ :=
  MonoidHom.coe_mulStarInv_apply _ _ g

/-- The component of `ι_w(g)` at `w` is `g`. -/
@[simp]
theorem proj_ofSplitPlace_self (g : GL ι (w.adicCompletion E)) :
    proj E ι w (ofSplitPlace E ι w hw g) = g := by
  rw [proj_eq_map, coe_ofSplitPlace, map_mul, map_inv, map_proj_ofAdicCompletionGL_self,
    map_proj_star_ofAdicCompletionGL_of_ne hw.symm, inv_one, mul_one]

/-- The component of `ι_w(g)` at `conj w` is `(σ(g)⁻¹)ᵀ`, for the isomorphism
`σ : E_w ≃ E_{conj w}` extending the conjugation of `E`. -/
@[simp]
theorem proj_conjPlace_ofSplitPlace (g : GL ι (w.adicCompletion E)) :
    proj E ι w.conjPlace (ofSplitPlace E ι w hw g) =
      GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map
        (adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w) :
          w.adicCompletion E →+* w.conjPlace.adicCompletion E) g) := by
  rw [proj_eq_map, coe_ofSplitPlace, map_mul, map_proj_ofAdicCompletionGL_of_ne hw, one_mul,
    map_proj_conjPlace_star_inv, map_proj_ofAdicCompletionGL_self]

/-- The component of `ι_w(g)` at a place other than `w` and `conj w` is `1`. -/
@[simp]
theorem proj_ofSplitPlace_of_ne {u : HeightOneSpectrum (𝓞 E)} (hu : u ≠ w)
    (hu' : u ≠ w.conjPlace) (g : GL ι (w.adicCompletion E)) :
    proj E ι u (ofSplitPlace E ι w hw g) = 1 := by
  rw [proj_eq_map, coe_ofSplitPlace, map_mul, map_inv, map_proj_ofAdicCompletionGL_of_ne hu,
    map_proj_star_ofAdicCompletionGL_of_ne hu', inv_one, mul_one]

/-- The component at `w` is a left inverse of `ι_w`. -/
theorem leftInverse_proj_ofSplitPlace :
    Function.LeftInverse (proj E ι w) (ofSplitPlace E ι w hw) :=
  proj_ofSplitPlace_self hw

/-- `ι_w` is injective. -/
theorem ofSplitPlace_injective : Function.Injective (ofSplitPlace E ι w hw) :=
  (leftInverse_proj_ofSplitPlace hw).injective

/-- `ι_w` is continuous. -/
theorem continuous_ofSplitPlace : Continuous (ofSplitPlace E ι w hw) := by
  have hy := continuous_ofAdicCompletionGL (ι := ι) (K := E) w
  exact continuous_induced_rng.2 <|
    (continuous_congr (coe_ofSplitPlace hw)).2 (hy.mul hy.star.inv)

/-- **The image of `ι_w`** is the set of elements of `G_f` supported on `{w, conj w}`: those whose
component at every place other than `w` and `conj w` is `1`. -/
theorem range_ofSplitPlace :
    Set.range (ofSplitPlace E ι w hw) =
      {g | ∀ u, u ≠ w → u ≠ w.conjPlace → proj E ι u g = 1} := by
  ext x
  refine ⟨?_, fun hx ↦ ⟨proj E ι w x, Subtype.ext <| generalLinearGroup_ext fun u ↦ ?_⟩⟩
  · rintro ⟨g, rfl⟩ u hu hu'
    exact proj_ofSplitPlace_of_ne hw hu hu' g
  · rw [← proj_eq_map, ← proj_eq_map]
    rcases eq_or_ne u w with rfl | hu
    · exact proj_ofSplitPlace_self hw _
    rcases eq_or_ne u w.conjPlace with rfl | hu'
    · rw [proj_conjPlace_ofSplitPlace, proj_conjPlace]
    · rw [proj_ofSplitPlace_of_ne hw hu hu', hx u hu hu']

/-- The conjugate inverse transpose of an element of `GL_n(𝒪_w)` lies in `GL_n(𝒪_{conj w})`. -/
private theorem inverseTranspose_map_mem_range {g : GL ι (w.adicCompletion E)}
    (hg : g ∈ (GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers E).subtype).range) :
    GeneralLinearGroup.inverseTranspose (GeneralLinearGroup.map
        (adicCompletionCongr w w.conjPlace (complexConj E).toRingEquiv (valuation_conjPlace w) :
          w.adicCompletion E →+* w.conjPlace.adicCompletion E) g) ∈
      (GeneralLinearGroup.map (n := ι) (w.conjPlace.adicCompletionIntegers E).subtype).range := by
  -- membership in `GL_n(𝒪)` is integrality of the entries and of the inverse entries
  have hS (v : HeightOneSpectrum (𝓞 E)) (x : v.adicCompletion E) :
      x ∈ (v.adicCompletionIntegers E).subtype.range ↔ x ∈ v.adicCompletionIntegers E :=
    ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.property, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩
  rw [GeneralLinearGroup.mem_range_map_iff_of_injective (ValuationSubring.subtype_injective _)]
    at hg ⊢
  simp only [hS] at hg ⊢
  refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
  · rw [GeneralLinearGroup.coe_inverseTranspose, transpose_apply, ← map_inv,
      GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom,
      adicCompletionCongr_mem_adicCompletionIntegers_iff]
    exact hg.2 j i
  · rw [← map_inv, GeneralLinearGroup.coe_inverseTranspose, inv_inv, transpose_apply,
      GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom,
      adicCompletionCongr_mem_adicCompletionIntegers_iff]
    exact hg.1 j i

/-- **`ι_w(g)` lies in `K₀` exactly when `g ∈ GL_n(𝒪_w)`.** -/
theorem ofSplitPlace_mem_integralAdelicUnitaryGroup_iff {g : GL ι (w.adicCompletion E)} :
    ofSplitPlace E ι w hw g ∈ integralAdelicUnitaryGroup E ι ↔
      g ∈ (GeneralLinearGroup.map (n := ι) (w.adicCompletionIntegers E).subtype).range := by
  rw [mem_integralAdelicUnitaryGroup_iff_forall_place]
  refine ⟨fun h ↦ proj_ofSplitPlace_self hw g ▸ h w, fun hg u ↦ ?_⟩
  rcases eq_or_ne u w with rfl | hu
  · rwa [proj_ofSplitPlace_self]
  rcases eq_or_ne u w.conjPlace with rfl | hu'
  · rw [proj_conjPlace_ofSplitPlace]
    exact inverseTranspose_map_mem_range hg
  · rw [proj_ofSplitPlace_of_ne hw hu hu']
    exact one_mem _

end finiteAdelicUnitaryGroup

end TauCeti
