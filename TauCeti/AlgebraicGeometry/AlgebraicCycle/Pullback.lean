/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Length
public import TauCeti.AlgebraicGeometry.Fibers.GenericPoint
public import TauCeti.Topology.LocallyFinsupp.Comap
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.LocalRing.Length

/-!
# Pullback of algebraic cycles

Let `f : X ⟶ Y` be a morphism of schemes. The pullback of a cycle `α = Σ n_y [y]` on `Y` is the
cycle on `X` whose coefficient at `x` is `n_{f x} · m_f(x)`. The multiplicity `m_f(x)` is, at a
generic point `x` of its fibre (`AlgebraicGeometry.Scheme.Hom.IsFiberGenericPoint`), the length
`length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the fibre, read in `ℕ` (so `0`
if that length is infinite; it is finite when `X` is locally Noetherian), and `0` at the other
points. Thus `f^*[y] = Σ_x m_f(x) [x]`, the sum over the generic points `x` of the fibre of `f`
over `y`. For `f` flat of pure relative dimension between schemes locally of finite type over a
field, this is the flat pullback of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA); the version on cycles of
fixed dimension is `TauCeti.AlgebraicGeometry.Chow.cyclesPullback`.

## Main definitions and results

* `AlgebraicGeometry.AlgebraicCycle.pullbackMultiplicity f x`: the multiplicity `m_f(x)`.
* `AlgebraicGeometry.AlgebraicCycle.pullback f`: the pullback
  `AlgebraicCycle Y R →+ AlgebraicCycle X R`, for `X` locally Noetherian.
* `AlgebraicGeometry.AlgebraicCycle.pullback_eq_comap_of_isOpenImmersion`: along an open
  immersion the multiplicities are one
  (`AlgebraicGeometry.AlgebraicCycle.pullbackMultiplicity_eq_one_of_isOpenImmersion`), and the
  pullback is the restriction `α ↦ α ∘ f`
* `AlgebraicGeometry.AlgebraicCycle.pullbackMultiplicity_pos_iff`: for `X` locally Noetherian,
  `m_f(x)` is positive exactly at the generic points of the fibres, where the local ring of the
  fibre has finite length
  (`AlgebraicGeometry.AlgebraicCycle.length_ne_top_of_isFiberGenericPoint`).
* `AlgebraicGeometry.AlgebraicCycle.pullbackMultiplicity_comp` and
  `AlgebraicGeometry.AlgebraicCycle.pullback_comp`: for `f` flat, `m_{g ∘ f}(x) = m_g(f x) · m_f(x)`
  and `(g ∘ f)^* = f^* ∘ g^*`.
-/

public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {R : Type*} [Semiring R] {X Y : Scheme.{u}}

open scoped Classical in
/-- The multiplicity of the pullback of cycles along `f : X ⟶ Y` at `x`: for `x` a generic point
of its fibre, the length `length_{O_{X,x}} (O_{X,x} / m_{f x} O_{X,x})` of the local ring of the
fibre at `x`, read in `ℕ` through `ENat.toNat` (so `0` if the length is infinite; it is finite and
positive when `X` is locally Noetherian); zero at the other points. -/
noncomputable def pullbackMultiplicity (f : X ⟶ Y) (x : X) : ℕ :=
  if f.IsFiberGenericPoint x then
    (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat
  else 0

/-- At a generic point of its fibre, the multiplicity is the length of the local ring of the
fibre, through `ENat.toNat`. -/
lemma pullbackMultiplicity_of_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : f.IsFiberGenericPoint x) :
    pullbackMultiplicity f x =
      (Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat := by
  simp only [pullbackMultiplicity, hx, ↓reduceIte]

/-- At a point which is not a generic point of its fibre, the multiplicity is zero. -/
@[simp]
lemma pullbackMultiplicity_of_not_isFiberGenericPoint (f : X ⟶ Y) {x : X}
    (hx : ¬ f.IsFiberGenericPoint x) : pullbackMultiplicity f x = 0 := by
  simp only [pullbackMultiplicity, hx, ↓reduceIte]

/-- A point with nonzero multiplicity is a generic point of its fibre. -/
lemma isFiberGenericPoint_of_pullbackMultiplicity_ne_zero (f : X ⟶ Y) {x : X}
    (hx : pullbackMultiplicity f x ≠ 0) : f.IsFiberGenericPoint x := by
  by_contra h
  exact hx (pullbackMultiplicity_of_not_isFiberGenericPoint f h)

/-- Along an open immersion every multiplicity is one. -/
@[simp]
lemma pullbackMultiplicity_eq_one_of_isOpenImmersion (f : X ⟶ Y) [IsOpenImmersion f]
    (x : X) : pullbackMultiplicity f x = 1 := by
  -- The fibre over `f x` is the single point `x`, and the stalk map is an isomorphism, so the
  -- local ring of the fibre is the residue field.
  rw [pullbackMultiplicity_of_isFiberGenericPoint f (f.isFiberGenericPoint_of_isPreimmersion x)]
  have hmap : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.map_isMaximal_of_equiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv)
  have : IsSimpleModule (X.presheaf.stalk x)
      (X.presheaf.stalk x ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [hmap, Module.length_eq_one, ENat.toNat_one]

/-- At a generic point `x` of its fibre, every prime of `O_{X,x}` containing `m_{f x} O_{X,x}` is
the maximal ideal: it is a generization of `x` in the fibre of `f`, hence `x` itself. -/
private lemma eq_maximalIdeal_of_map_le (f : X ⟶ Y) {x : X} (hx : f.IsFiberGenericPoint x)
    (p : Ideal (X.presheaf.stalk x)) [p.IsPrime]
    (hp : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom ≤ p) :
    p = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  let P : Spec (X.presheaf.stalk x) := ⟨p, inferInstance⟩
  -- The image of `P` in `Spec O_{Y, f x}` is the closed point, so `P` lies over `f x`.
  have hP : Spec.map (f.stalkMap x) P = IsLocalRing.closedPoint (Y.presheaf.stalk (f x)) := by
    rw [Spec.map_apply]
    refine PrimeSpectrum.ext ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
      (Ideal.IsPrime.comap (f.stalkMap x).hom).ne_top (Ideal.map_le_iff_le_comap.mp hp)).symm
  have hfP : f (X.fromSpecStalk x P) = f x := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply,
      hP, Scheme.fromSpecStalk_closedPoint]
  have hPx : X.fromSpecStalk x P ⤳ x := by
    have h : X.fromSpecStalk x P ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self P
    rwa [Scheme.range_fromSpecStalk] at h
  have h := (f.isFiberGenericPoint_iff_forall_specializes x).mp hx _ hfP hPx
  exact congrArg PrimeSpectrum.asIdeal ((X.fromSpecStalk x).isEmbedding.injective
    (h.trans Scheme.fromSpecStalk_closedPoint.symm))

/-- For `X` locally Noetherian, at a generic point `x` of its fibre the local ring of the fibre
`O_{X,x} ⧸ m_{f x} O_{X,x}` has finite length: the maximal ideal is the only prime containing
`m_{f x} O_{X,x}`, so that ideal has maximal radical. -/
lemma length_ne_top_of_isFiberGenericPoint [IsLocallyNoetherian X] (f : X ⟶ Y) {x : X}
    (hx : f.IsFiberGenericPoint x) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x ⧸
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom) ≠ ⊤ := by
  set I := (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom
  have hI : I.radical = IsLocalRing.maximalIdeal _ := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal ?_) ?_
    · rw [Ne, Ideal.radical_eq_top]
      exact (IsLocalRing.map_maximalIdeal_lt_top _).ne
    · rw [Ideal.radical_eq_sInf]
      exact le_sInf fun J ⟨hJ, _⟩ ↦ (eq_maximalIdeal_of_map_le f hx J hJ).ge
  exact Module.length_ne_top_iff.mpr (Ideal.isFiniteLength_quotient_of_isMaximal_radical I
    (hI ▸ IsLocalRing.maximalIdeal.isMaximal _))

/-- For `X` locally Noetherian, the multiplicity `m_f(x)` is positive exactly at the generic points
of the fibres: there it is the length of a nonzero Artinian local ring
(`length_ne_top_of_isFiberGenericPoint`). -/
lemma pullbackMultiplicity_pos_iff [IsLocallyNoetherian X] (f : X ⟶ Y) (x : X) :
    0 < pullbackMultiplicity f x ↔ f.IsFiberGenericPoint x := by
  refine ⟨fun h ↦ isFiberGenericPoint_of_pullbackMultiplicity_ne_zero f h.ne', fun hx ↦ ?_⟩
  rw [pullbackMultiplicity_of_isFiberGenericPoint f hx]
  refine ENat.toNat_pos ?_ (length_ne_top_of_isFiberGenericPoint f hx)
  rw [← pos_iff_ne_zero, Module.length_pos_iff, Ideal.Quotient.nontrivial_iff]
  exact (IsLocalRing.map_maximalIdeal_lt_top _).ne

/-- For `X` locally Noetherian, the pullback `f^* α`, with coefficient `α (f x) · m_f(x)` at `x`,
has locally finite support. -/
private lemma locallyFiniteSupport_mul_pullbackMultiplicity [IsLocallyNoetherian X]
    (f : X ⟶ Y) (α : AlgebraicCycle Y R) :
    LocallyFiniteSupport fun x ↦ α (f x) * pullbackMultiplicity f x := by
  -- An affine open `U` of `X` has compact image, which meets the support of `α` in finitely many
  -- points, and `U` contains finitely many generic points of each fibre.
  intro z
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  refine ⟨U, U.isOpen.mem_nhds hzU, ?_⟩
  have hF : (f '' (U : Set X) ∩ Function.support α).Finite :=
    (Function.locallyFinsupp.locallyFiniteSupport α).finite_inter_support_of_isCompact
      (hU.isCompact.image f.continuous)
  refine (hF.biUnion fun y _ ↦
    f.finite_setOf_mem_and_apply_eq_and_isFiberGenericPoint U.isOpen y).subset ?_
  rintro x ⟨hxU, hx⟩
  have hm : pullbackMultiplicity f x ≠ 0 := fun h ↦
    right_ne_zero_of_mul hx (by rw [h, Nat.cast_zero])
  exact Set.mem_biUnion (x := f x) ⟨⟨x, hxU, rfl⟩, left_ne_zero_of_mul hx⟩
    ⟨hxU, rfl, isFiberGenericPoint_of_pullbackMultiplicity_ne_zero f hm⟩

/-- The pullback of cycles along `f : X ⟶ Y`, for `X` locally Noetherian: the coefficient of
`f^* α` at `x` is `α (f x) · m_f(x)`, so `f^*[y] = Σ m_f(x) [x]` over the generic points `x` of
the fibre over `y`. For `f` flat of constant relative dimension between schemes locally of finite
type over a field, this is the flat pullback of
[Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA). -/
noncomputable def pullback [IsLocallyNoetherian X] (f : X ⟶ Y) :
    AlgebraicCycle Y R →+ AlgebraicCycle X R where
  toFun α :=
    { toFun x := α (f x) * pullbackMultiplicity f x
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' z _ :=
        locallyFiniteSupport_mul_pullbackMultiplicity f α z }
  map_zero' := by
    ext x
    exact zero_mul _
  map_add' α β := by
    ext x
    exact add_mul _ _ _

/-- The coefficient of a pullback at `x` is the coefficient at `f x` times the multiplicity. -/
@[simp]
lemma pullback_apply [IsLocallyNoetherian X] (f : X ⟶ Y) (α : AlgebraicCycle Y R) (x : X) :
    pullback f α x = α (f x) * pullbackMultiplicity f x :=
  (rfl)

/-- Along an open immersion, the pullback of cycles is the restriction `α ↦ α ∘ f`. -/
lemma pullback_eq_comap_of_isOpenImmersion [IsLocallyNoetherian X] (f : X ⟶ Y)
    [IsOpenImmersion f] (α : AlgebraicCycle Y R) :
    pullback f α =
      Function.locallyFinsupp.comap f f.continuous f.isOpenEmbedding.injective α := by
  ext x
  rw [pullback_apply, pullbackMultiplicity_eq_one_of_isOpenImmersion, Nat.cast_one,
    mul_one, Function.locallyFinsupp.comap_apply]

/-- Pulling back along the identity does nothing. -/
@[simp]
lemma pullback_id [IsLocallyNoetherian X] :
    pullback (R := R) (𝟙 X) = AddMonoidHom.id _ := by
  ext α x
  simp

section comp

variable {Z : Scheme.{u}}

/-- Along a flat `f`, the multiplicities of the pullback of cycles multiply:
`m_{g ∘ f}(x) = m_g(f x) · m_f(x)`. At a generic point of the fibre of `g ∘ f` this is the
multiplicativity of lengths along the flat local homomorphism `O_{Y, f x} → O_{X, x}`
(`IsLocalRing.length_quotient_map_comp`); flatness also makes `f x` a generic point of its
`g`-fibre (`AlgebraicGeometry.Scheme.Hom.isFiberGenericPoint_comp_iff_of_generalizingMap`). -/
lemma pullbackMultiplicity_comp (f : X ⟶ Y) [Flat f] (g : Y ⟶ Z) (x : X) :
    pullbackMultiplicity (f ≫ g) x = pullbackMultiplicity g (f x) * pullbackMultiplicity f x := by
  by_cases hx : (f ≫ g).IsFiberGenericPoint x
  · rw [pullbackMultiplicity_of_isFiberGenericPoint _ hx,
      pullbackMultiplicity_of_isFiberGenericPoint _
        (hx.of_comp_of_generalizingMap (Flat.generalizingMap f)),
      pullbackMultiplicity_of_isFiberGenericPoint _ hx.of_comp, ← ENat.toNat_mul]
    congr 1
    rw [Scheme.Hom.stalkMap_comp]
    exact IsLocalRing.length_quotient_map_comp (g.stalkMap (f x)).hom (f.stalkMap x).hom
      (Flat.stalkMap f x) _
  · rw [pullbackMultiplicity_of_not_isFiberGenericPoint _ hx]
    by_cases hf : f.IsFiberGenericPoint x
    · rw [pullbackMultiplicity_of_not_isFiberGenericPoint g fun hg ↦ hx (hg.comp hf), zero_mul]
    · rw [pullbackMultiplicity_of_not_isFiberGenericPoint f hf, mul_zero]

/-- Pullback of cycles is functorial along flat morphisms: `(g ∘ f)^* = f^* ∘ g^*` for `f` flat,
by the multiplicativity of the multiplicities (`pullbackMultiplicity_comp`). This is the
functoriality of flat pullback of [Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA)
and Fulton, *Intersection Theory*, §1.7. -/
lemma pullback_comp [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) [Flat f]
    (g : Y ⟶ Z) :
    pullback (R := R) (f ≫ g) = (pullback f).comp (pullback g) := by
  ext α x
  simp only [pullback_apply, AddMonoidHom.comp_apply, pullbackMultiplicity_comp, Nat.cast_mul,
    mul_assoc, Scheme.Hom.comp_apply]

end comp

end AlgebraicGeometry.AlgebraicCycle
