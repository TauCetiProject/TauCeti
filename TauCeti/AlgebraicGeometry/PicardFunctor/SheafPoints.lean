/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.FieldExtension
public import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
public import TauCeti.AlgebraicGeometry.PicardFunctor.Fppf

/-!
# The points of the relative Picard sheaf over the base

For a morphism of schemes `f : X ⟶ S`, the group `Pic_{X/S}(S)` of sections of the relative Picard
fppf sheaf over `S` itself (`TauCeti.AlgebraicGeometry.picardSheafPoints`) receives a homomorphism
from the Picard group of `X` (`TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass`),
sending a line bundle to its class.

When `S = Spec k` and `X` is a curve without a rational point, this homomorphism need not be
surjective: an element of `Pic_{X/k}(k)` is a line-bundle class given only fppf-locally on
`Spec k`, which need not come from a line bundle on `X`. For the pointless real conic,
`Pic(X) = 2ℤ` while `Pic_{X/ℝ}(ℝ) = ℤ`. When `X` is a smooth proper geometrically integral curve
over `k`, the elements of `Pic_{X/k}(k)` are the `k`-rational divisor classes of `X`
(Poonen–Stoll, Section 2); this file proves no such divisor comparison.

The homomorphism is injective for an integral scheme universally closed and quasi-separated over
a field (`TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass_injective`), so `Pic(X)`
is a subgroup of the `k`-points `Pic_{X/k}(k)` of the relative Picard sheaf. An element of
`Pic(X)` that vanishes in `Pic_{X/k}(k)` is trivial on some fppf cover of `Spec k`, hence on
`X_K` for a field `K` over a point of the cover; and under these hypotheses, a line bundle that
becomes trivial after a field extension is trivial
(`TauCeti.AlgebraicGeometry.LineBundleClass.pullback_injective`). The scheme need not be smooth
or geometrically integral, and no dimension bound or cohomological finiteness assumption is
needed.

## Main declarations

* `TauCeti.AlgebraicGeometry.picardSheafPoints`: the group `Pic_{X/S}(S)`;
* `TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass`: the homomorphism
  `Pic(X) → Pic_{X/S}(S)`;
* `TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass_injective`: it is injective
  for an integral scheme universally closed and quasi-separated over a field.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
* B. Poonen, M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Ann. of Math.
  150 (1999), Section 2.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The group `Pic_{X/S}(S)` of sections over `S` of the relative Picard fppf sheaf of
`f : X ⟶ S`. For `S = Spec k` these are the `k`-points `Pic_{X/k}(k)` of the relative Picard
sheaf, which need not be classes of line bundles on `X` when `X` has no rational point; for a
smooth proper geometrically integral curve over `k` they are its `k`-rational divisor classes. -/
-- Exposed so that the sections of the relative Picard sheaf over `S` are its elements.
@[expose]
def picardSheafPoints : AddCommGrpCat.{u + 1} :=
  (relativePicardFppfSheaf f).obj.obj (op (Over.mk (𝟙 S)))

/-- The points are the sections of the relative Picard fppf sheaf over the identity of the base. -/
lemma picardSheafPoints_eq :
    picardSheafPoints f = (relativePicardFppfSheaf f).obj.obj (op (Over.mk (𝟙 S))) := rfl

namespace picardSheafPoints

/-- The homomorphism `Pic(X) → Pic_{X/S}(S)` sending the class of a line bundle on `X` to its
section of the relative Picard sheaf. It is the image of the class on `X ≅ S ×_S X` in
`Pic(X) / Pic(S)`, followed by the canonical map to the sheafification. -/
def ofLineBundleClass : Additive (LineBundleClass X) →+ picardSheafPoints f :=
  ((relativePicardToFppfSheaf f).app (op (Over.mk (𝟙 S)))).hom.comp <|
    AddMonoidHom.mk'
      (fun a ↦ relativePicardAddPresheafMk f _
        (LineBundleClass.pullback (pullback.snd (𝟙 S) f) a.toMul))
      fun a b ↦ by rw [toMul_add, LineBundleClass.pullback_mul, relativePicardAddPresheafMk_mul]

/-- The section of the relative Picard sheaf attached to a line-bundle class on `X` is the image
of its pullback to `S ×_S X` under the canonical map to the sheafification. -/
lemma ofLineBundleClass_apply (a : Additive (LineBundleClass X)) :
    ofLineBundleClass f a = (relativePicardToFppfSheaf f).app (op (Over.mk (𝟙 S)))
      (relativePicardAddPresheafMk f (op (Over.mk (𝟙 S)))
        (LineBundleClass.pullback (pullback.snd (𝟙 S) f) a.toMul)) :=
  (rfl)

/-- Line-bundle classes pulled back from the base vanish in the relative Picard sheaf. -/
@[simp]
lemma ofLineBundleClass_pullback (b : LineBundleClass S) :
    ofLineBundleClass f (Additive.ofMul (LineBundleClass.pullback f b)) = 0 := by
  rw [ofLineBundleClass_apply, toMul_ofMul, LineBundleClass.pullback_comp, ← pullback.condition,
    ← LineBundleClass.pullback_comp, LineBundleClass.pullback_id]
  exact (congrArg ((relativePicardToFppfSheaf f).app (op (Over.mk (𝟙 S))))
    (relativePicardAddPresheafMk_pullback_fst f (op (Over.mk (𝟙 S))) b)).trans (map_zero _)

/-- Restricting the section attached to a line bundle on `X` to `T` gives the class of its
pullback to `X_T = T ×_S X`. -/
lemma map_ofLineBundleClass {T : (Over S)ᵒᵖ} (φ : op (Over.mk (𝟙 S)) ⟶ T)
    (a : Additive (LineBundleClass X)) :
    (relativePicardFppfSheaf f).obj.map φ (ofLineBundleClass f a) =
      (relativePicardToFppfSheaf f).app T
        (relativePicardAddPresheafMk f T
          (LineBundleClass.pullback (pullback.snd T.unop.hom f) a.toMul)) := by
  rw [ofLineBundleClass_apply, ← ConcreteCategory.comp_apply,
    ← (relativePicardToFppfSheaf f).naturality, ConcreteCategory.comp_apply,
    relativePicardAddPresheaf_map_mk, LineBundleClass.pullback_comp]
  simp only [Over.Hom.left, Over.pullback_map_left]
  apply congrArg ((relativePicardToFppfSheaf f).app T)
  apply congrArg (relativePicardAddPresheafMk f T)
  exact congrArg (LineBundleClass.pullback · a.toMul) (pullback.lift_snd _ _ _)

/-- If the class of a line bundle on `X` vanishes in `Pic_{X/S}(S)`, then for every point of `S`
there are a field `K` and a `K`-point `ψ : Spec K ⟶ S` through it over which the line bundle
becomes trivial on the fibre `Spec K ×_S X`. -/
theorem exists_pullback_eq_one_of_ofLineBundleClass_eq_zero {a : LineBundleClass X}
    (ha : ofLineBundleClass f (Additive.ofMul a) = 0) (s : S) :
    ∃ (K : Type u) (_ : Field K) (ψ : Spec (.of K) ⟶ S),
      s ∈ Set.range ψ ∧ LineBundleClass.pullback (pullback.snd ψ f) a = 1 := by
  let T₀ : (Over S)ᵒᵖ := op (Over.mk (𝟙 S))
  let c := relativePicardAddPresheafMk f T₀ (LineBundleClass.pullback (pullback.snd (𝟙 S) f) a)
  -- The section `c` vanishes on an fppf covering sieve of `S`.
  have hc := Presheaf.equalizerSieve_mem (Scheme.fppfTopology.over S)
    (relativePicardToFppfSheaf f) c 0
    (by rw [map_zero]; rwa [ofLineBundleClass_apply, toMul_ofMul] at ha)
  rw [GrothendieckTopology.mem_over_iff] at hc
  -- Some member `g : U ⟶ S` of an fppf covering family inside this sieve has a point `u` over
  -- `s`; pass to the residue field of `u`.
  have : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hc
  obtain ⟨R, ⟨hsurj, -⟩, hRc⟩ := hc
  obtain ⟨_, _, hg, u, hu⟩ := hsurj s
  cases hg with
  | @of U g hg =>
  let ψ : Spec (.of (U.residueField u)) ⟶ S := U.fromSpecResidueField u ≫ g
  have hψ : (Sieve.overEquiv (unop T₀) (Presheaf.equalizerSieve c 0)) ψ :=
    Sieve.downward_closed _ (hRc U g hg) _
  rw [Sieve.overEquiv_iff, Presheaf.equalizerSieve_apply, map_zero,
    relativePicardAddPresheaf_map_mk, relativePicardAddPresheafMk_eq_zero_iff] at hψ
  obtain ⟨p⟩ : Nonempty (Spec (U.residueField u)) := inferInstance
  have hψs : (U.fromSpecResidueField u ≫ g) p = s := by
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact hu
  refine ⟨_, inferInstance, ψ, ⟨_, hψs⟩, ?_⟩
  -- Every line bundle on the spectrum of a field is trivial, so the class on the fibre is trivial.
  obtain ⟨b, hb⟩ := hψ
  rw [Subsingleton.elim (α := LineBundleClass (Spec (.of (U.residueField u)))) b 1, map_one,
    LineBundleClass.pullback_comp] at hb
  have key : LineBundleClass.pullback (pullback.snd (ψ ≫ 𝟙 S) f) a = 1 := by
    rw [hb]
    simp only [Over.Hom.left, Over.pullback_map_left]
    exact congrArg (LineBundleClass.pullback · a) (pullback.lift_snd _ _ _).symm
  rwa [Category.comp_id] at key

/-- **The Picard group embeds in the `k`-points of the relative Picard sheaf.** For an integral
scheme `X` universally closed and quasi-separated over a field `k` (for instance proper), the
homomorphism `Pic(X) → Pic_{X/k}(k)` is injective, even without a rational point. No dimension
bound or cohomological finiteness assumption is needed; the map need not be surjective. -/
theorem ofLineBundleClass_injective {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    [IsIntegral X] [UniversallyClosed f] [QuasiSeparated f] :
    Function.Injective (ofLineBundleClass f) := by
  rw [injective_iff_map_eq_zero, Additive.forall]
  intro a ha
  -- `a` becomes trivial on the fibre over some `K`-point of `Spec k`.
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨K, _, ψ, -, hψ⟩ := exists_pullback_eq_one_of_ofLineBundleClass_eq_zero _ ha s
  -- That fibre is the base change of `X` along the field extension `k → K` defined by `ψ`.
  let _ : Algebra k K := (Spec.preimage ψ).hom.toAlgebra
  have hξ : Spec.map (CommRingCat.ofHom (algebraMap k K)) = ψ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  have H : IsPullback (pullback.snd ψ f)
      (pullback.fst ψ f) f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [hξ]
    exact (IsPullback.of_hasPullback ψ _).flip
  rw [ofMul_eq_zero]
  exact LineBundleClass.pullback_injective H (by rw [hψ, LineBundleClass.pullback_one])

end picardSheafPoints

end

end TauCeti.AlgebraicGeometry
