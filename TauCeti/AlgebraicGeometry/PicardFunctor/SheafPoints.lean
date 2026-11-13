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
`Pic(X) = 2ℤ` while `Pic_{X/ℝ}(ℝ) = ℤ`. The elements of `Pic_{X/k}(k)` are called the `k`-rational
divisor classes of `X`.

The homomorphism is injective for a proper integral curve over a field
(`TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass_injective`), so `Pic(X)` is a
subgroup of the `k`-rational divisor classes. An element of `Pic(X)` that vanishes in
`Pic_{X/k}(k)` is trivial on some fppf cover of `Spec k`, hence on `X_K` for a field `K` over a
point of the cover; and on a proper integral curve, a line bundle that becomes trivial after a
field extension is trivial (`TauCeti.AlgebraicGeometry.LineBundleClass.pullback_injective`).
The curve need not be smooth or geometrically integral.

## Main declarations

* `TauCeti.AlgebraicGeometry.picardSheafPoints`: the group `Pic_{X/S}(S)`;
* `TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass`: the homomorphism
  `Pic(X) → Pic_{X/S}(S)`;
* `TauCeti.AlgebraicGeometry.picardSheafPoints.ofLineBundleClass_injective`: it is injective
  for a proper integral curve over a field.

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
`f : X ⟶ S`. For `S = Spec k` these are the `k`-rational divisor classes of `X`, which need not
be classes of line bundles on `X` when `X` has no rational point. -/
-- Exposed so that the sections of the relative Picard sheaf over `S` are its elements.
@[expose]
def picardSheafPoints : AddCommGrpCat.{u + 1} :=
  (relativePicardFppfSheaf f).obj.obj (op (Over.mk (𝟙 S)))

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
      (relativePicardAddPresheafMk f _
        (LineBundleClass.pullback (pullback.snd (𝟙 S) f) a.toMul)) :=
  (rfl)

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
    (relativePicardToFppfSheaf f) c 0 (by rw [map_zero]; exact ha)
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
    exact congrArg (LineBundleClass.pullback · a) (pullback.lift_snd _ _ _).symm
  rwa [Category.comp_id] at key

variable {k : Type u} [Field k] [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))] [RelativeDimensionLE 1 (X ↘ Spec (.of k))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The Picard group of a proper integral curve embeds in the rational divisor classes.** For a
proper integral curve `X` over a field `k`, the homomorphism `Pic(X) → Pic_{X/k}(k)` is injective,
even when `X` has no rational point; it need not be surjective. -/
theorem ofLineBundleClass_injective :
    Function.Injective (ofLineBundleClass (X ↘ Spec (.of k))) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  -- `a` becomes trivial on the fibre over some `K`-point of `Spec k`.
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
  obtain ⟨K, _, ψ, -, hψ⟩ := exists_pullback_eq_one_of_ofLineBundleClass_eq_zero _ ha s
  -- That fibre is the base change of `X` along the field extension `k → K` defined by `ψ`.
  let _ : Algebra k K := (Spec.preimage ψ).hom.toAlgebra
  have hξ : Spec.map (CommRingCat.ofHom (algebraMap k K)) = ψ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_preimage]
  let _ : (pullback ψ (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨pullback.fst _ _⟩
  have H : IsPullback (pullback.snd ψ (X ↘ Spec (.of k)))
      (pullback ψ (X ↘ Spec (.of k)) ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [hξ]
    exact (IsPullback.of_hasPullback ψ _).flip
  exact congrArg Additive.ofMul
    (LineBundleClass.pullback_injective H (by rw [hψ, LineBundleClass.pullback_one]))

end picardSheafPoints

end

end TauCeti.AlgebraicGeometry
