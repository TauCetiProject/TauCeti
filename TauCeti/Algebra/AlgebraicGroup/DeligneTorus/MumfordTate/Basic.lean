/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DeligneTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Contraction

/-!
# The Mumford–Tate group of a homomorphism from the Deligne torus

Let `G` be an affine group over `ℚ` with coordinate Hopf algebra `H`, and let `h : S → G_ℝ` be a
homomorphism of real algebraic groups from the Deligne torus `S = Res_{ℂ/ℝ} 𝔾ₘ`. On coordinate
rings `h` is a morphism of commutative Hopf `ℝ`-algebras `ℝ ⊗[ℚ] H ⟶ O(S)`. For `G = GL(V)` with
`V` a finite-dimensional `ℚ`-vector space, such an `h` whose weight is defined over `ℚ` is a
rational Hodge structure on `V`; for a Shimura datum `(G, X)` it is a point `h ∈ X`.

The **Mumford–Tate group** `MT(h)` is the smallest closed subgroup of `G`, defined over `ℚ`,
through whose real extension `h` factors. Closed `ℚ`-subgroups of `G` correspond to Hopf ideals of
`H`, and `h` factors through the real extension of the subgroup cut out by a Hopf ideal `I`
exactly when `h` kills the base change `I_ℝ`. So `MT(h)` is cut out by the largest Hopf ideal of
`H` whose real extension `h` kills: the contraction to `ℚ` of the largest Hopf ideal of
`ℝ ⊗[ℚ] H` killed by `h` (`TauCeti.CommHopfAlgCat.contractHopfIdeal`). As a supremum of Hopf
ideals it needs no argument that the kernel of `H → ℝ ⊗[ℚ] H → O(S)` is itself a Hopf ideal.

## Main declarations

* `TauCeti.DeligneTorus.mumfordTateHopfIdeal h`: the Hopf ideal of `H` cutting out `MT(h)`, the
  Hopf-ideal contraction of the largest Hopf ideal contained in the kernel of the coordinate map
  of `h` (`TauCeti.DeligneTorus.mumfordTateHopfIdeal_def`).
* `TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff`: **minimality**; `MT(h)` is contained in
  the closed `ℚ`-subgroup cut out by `I` exactly when `h` kills `I_ℝ`.
* `TauCeti.DeligneTorus.mumfordTateLift`,
  `TauCeti.DeligneTorus.baseChangeMap_mkQuotient_comp_mumfordTateLift` and
  `TauCeti.DeligneTorus.mumfordTateLift_unique`: `h` factors uniquely through the
  real extension of `MT(h)`.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_toIdeal_le_ker`: a homomorphism into `G` defined
  over `ℚ` whose real extension factors through `h` lands in `MT(h)`.
* `TauCeti.DeligneTorus.mumfordTateHopfIdeal_eq_augmentation_iff`: `MT(h)` is trivial exactly
  when `h` is trivial.
* `TauCeti.DeligneTorus.comapOfSurjective_mumfordTateHopfIdeal`: an isomorphism of affine groups
  over `ℚ` carries the Mumford–Tate group of `h` to that of its composite with `h`.
* `TauCeti.DeligneTorus.mumfordTateQuotientIsoOfIso`: for an isomorphism `e : H ≅ L` of
  coordinate Hopf algebras, the coordinate isomorphism between the Mumford–Tate group of `h` and
  that of its twist by `e`.
* `TauCeti.DeligneTorus.exists_finset_sup_eq_mumfordTateHopfIdeal`: for noetherian `H`, `MT(h)`
  is the intersection of finitely many closed `ℚ`-subgroups through which `h` factors.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §2, p. 31 (the aside after Definition 2.16),
  for the Mumford–Tate group of a rational Hodge structure, and §5, for that of a point of a
  Shimura datum.
* P. Deligne, *Hodge cycles on abelian varieties* (notes by J. S. Milne), §3, pp. 24–25.
-/

public section

open CategoryTheory _root_.CommHopfAlgCat TauCeti.CommHopfAlgCat

namespace TauCeti.DeligneTorus

variable {H L : _root_.CommHopfAlgCat.{0} ℚ}

/-- **The Mumford–Tate group** of a homomorphism `h : S → G_ℝ` from the Deligne torus to the real
extension of an affine group `G` over `ℚ` with coordinate Hopf algebra `H`, as the Hopf ideal of
`H` cutting it out: the largest Hopf ideal of `H` whose real extension is killed by `h`.
Contravariantly, `MT(h)` is the smallest closed `ℚ`-subgroup of `G` through whose real extension
`h` factors (`TauCeti.DeligneTorus.le_mumfordTateHopfIdeal_iff`). -/
noncomputable def mumfordTateHopfIdeal
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) : HopfIdeal ℚ H :=
  contractHopfIdeal (commonKernelHopfIdeal fun _ : Unit ↦ h)

/-- The Mumford–Tate ideal is the contraction to `ℚ` of the largest Hopf ideal killed by `h`. -/
theorem mumfordTateHopfIdeal_def
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateHopfIdeal h = contractHopfIdeal (commonKernelHopfIdeal fun _ : Unit ↦ h) := by
  rw [mumfordTateHopfIdeal]

/-- **Minimality of the Mumford–Tate group.** A Hopf ideal `I` lies below the Mumford–Tate ideal
of `h` exactly when `h` kills its real extension: the closed `ℚ`-subgroup cut out by `I`
contains `MT(h)` exactly when `h` factors through its real extension. -/
theorem le_mumfordTateHopfIdeal_iff
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S} {I : HopfIdeal ℚ H} :
    I ≤ mumfordTateHopfIdeal h ↔
      (baseChangeHopfIdeal (K := ℝ) I).toIdeal ≤ RingHom.ker h.hom.toAlgHom.toRingHom := by
  rw [mumfordTateHopfIdeal, le_contractHopfIdeal_commonKernelHopfIdeal_iff, forall_const]

/-- `h` kills the real extension of the Mumford–Tate ideal: `h` factors through the real
extension of `MT(h)`. -/
theorem baseChangeHopfIdeal_mumfordTateHopfIdeal_toIdeal_le_ker
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    (baseChangeHopfIdeal (K := ℝ) (mumfordTateHopfIdeal h)).toIdeal ≤
      RingHom.ker h.hom.toAlgHom.toRingHom :=
  le_mumfordTateHopfIdeal_iff.mp le_rfl

/-- **The factorization of `h` through its Mumford–Tate group**: the homomorphism
`S → MT(h)_ℝ` whose composite with the inclusion `MT(h)_ℝ → G_ℝ` is `h`
(`TauCeti.DeligneTorus.baseChangeMap_mkQuotient_comp_mumfordTateLift`). -/
noncomputable def mumfordTateLift (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    baseChange (K := ℝ) (quotient H (mumfordTateHopfIdeal h)) ⟶ _root_.CommHopfAlgCat.of ℝ S :=
  baseChangeLiftQuotient _ h (baseChangeHopfIdeal_mumfordTateHopfIdeal_toIdeal_le_ker h)

/-- Composing the factorization through `MT(h)_ℝ` with the inclusion into `G_ℝ` gives `h`. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_mkQuotient_comp_mumfordTateLift
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    baseChangeMap (K := ℝ) (mkQuotient H (mumfordTateHopfIdeal h)) ≫ mumfordTateLift h = h :=
  baseChangeMap_mkQuotient_comp_baseChangeLiftQuotient _ _ _

/-- The factorization through `MT(h)_ℝ` is the only morphism whose composite with the inclusion
`MT(h)_ℝ → G_ℝ` is `h`. -/
theorem mumfordTateLift_unique (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S)
    (g : baseChange (K := ℝ) (quotient H (mumfordTateHopfIdeal h)) ⟶ _root_.CommHopfAlgCat.of ℝ S)
    (hg : baseChangeMap (K := ℝ) (mkQuotient H (mumfordTateHopfIdeal h)) ≫ g = h) :
    g = mumfordTateLift h :=
  baseChangeLiftQuotient_unique _ _ _ g hg

/-- **Homomorphisms defined over `ℚ` through `h` land in the Mumford–Tate group.** Let
`f : M → G` be a homomorphism of affine groups over `ℚ` whose real extension factors through
`h`, as `M_ℝ → S → G_ℝ`. Then `f` lands in `MT(h)`: it kills the Mumford–Tate ideal. This
applies for instance to a weight cocharacter `𝔾ₘ → G` defined over `ℚ`. -/
theorem mumfordTateHopfIdeal_toIdeal_le_ker
    {h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S}
    {N : _root_.CommHopfAlgCat.{0} ℚ} (f : H ⟶ N)
    (g : _root_.CommHopfAlgCat.of ℝ S ⟶ baseChange (K := ℝ) N)
    (hfg : h ≫ g = baseChangeMap (K := ℝ) f) :
    (mumfordTateHopfIdeal h).toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom := by
  refine contractHopfIdeal_toIdeal_le_ker (algebraMap ℚ ℝ).injective _ f fun x hx ↦ ?_
  have hx := BialgHom.mem_ker_toAlgHom_toRingHom.mp (commonKernelHopfIdeal_toIdeal_le_ker _ () hx)
  rw [BialgHom.mem_ker_toAlgHom_toRingHom, ← hfg, _root_.CommHopfAlgCat.hom_comp,
    BialgHom.comp_apply, hx, map_zero]

/-- **The Mumford–Tate group is trivial exactly when `h` is trivial**: the Mumford–Tate ideal is
the augmentation ideal, cutting out the trivial subgroup, exactly when `h` is the trivial
homomorphism `x ↦ ε(x) · 1`. For a rational Hodge structure this says that `MT(V)` is trivial
exactly when `V` is purely of type `(0, 0)`. -/
theorem mumfordTateHopfIdeal_eq_augmentation_iff
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mumfordTateHopfIdeal h = HopfIdeal.augmentation ℚ H ↔
      ∀ x, h.hom x = algebraMap ℝ S (Coalgebra.counit (R := ℝ) x) := by
  rw [mumfordTateHopfIdeal, contractHopfIdeal_eq_augmentation_iff,
    le_commonKernelHopfIdeal_iff, forall_const]
  refine ⟨fun hh ↦ AlgHom.apply_eq_counit_of_augmentation_le_ker h.hom.toAlgHom hh,
    fun hh x hx ↦ ?_⟩
  have hx0 : Coalgebra.counit (R := ℝ) x = 0 :=
    (HopfIdeal.mem_augmentation _ _).mp (HopfIdeal.mem_toIdeal.mp hx)
  rw [BialgHom.mem_ker_toAlgHom_toRingHom, hh, hx0, map_zero]

/-- **Invariance under isomorphisms.** Let `e : H ≅ L` be an isomorphism of coordinate Hopf
algebras, contravariantly an isomorphism `G' ≅ G` of affine groups over `ℚ`, and let
`h : S → G'_ℝ`. The Mumford–Tate group of the composite `S → G'_ℝ → G_ℝ` is the image of that of
`h`: its ideal is the pullback of the Mumford–Tate ideal of `h` along `e`. For `G = GL(V)` and
`G' = GL(V')`, this is the transport of `MT(V)` to `MT(V')` by conjugation along a `ℚ`-linear
isomorphism `V ≅ V'` intertwining the Hodge structures. -/
theorem comapOfSurjective_mumfordTateHopfIdeal (e : H ≅ L)
    (h : baseChange (K := ℝ) L ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    (mumfordTateHopfIdeal h).comapOfSurjective e.hom.hom
        (ConcreteCategory.bijective_of_isIso e.hom).2 =
      mumfordTateHopfIdeal (baseChangeMap (K := ℝ) e.hom ≫ h) := by
  rw [mumfordTateHopfIdeal, mumfordTateHopfIdeal, comapOfSurjective_contractHopfIdeal,
    comapOfSurjective_commonKernelHopfIdeal]

/-- **The Mumford–Tate groups of `h` and of its twist by an isomorphism are isomorphic.** For an
isomorphism `e : H ≅ L` of coordinate Hopf algebras, contravariantly an isomorphism `G' ≅ G` of
affine groups over `ℚ`, and `h : S → G'_ℝ`, the coordinate isomorphism between the Mumford–Tate
group of the composite `S → G'_ℝ → G_ℝ` and that of `h`, induced by `e`. -/
noncomputable def mumfordTateQuotientIsoOfIso (e : H ≅ L)
    (h : baseChange (K := ℝ) L ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    quotient H (mumfordTateHopfIdeal (baseChangeMap (K := ℝ) e.hom ≫ h)) ≅
      quotient L (mumfordTateHopfIdeal h) :=
  quotientIsoOfComapEq e _ (comapOfSurjective_mumfordTateHopfIdeal e h)

/-- The isomorphism of Mumford–Tate groups induced by `e` commutes with their embeddings into the
ambient groups. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_mumfordTateQuotientIsoOfIso_hom (e : H ≅ L)
    (h : baseChange (K := ℝ) L ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mkQuotient H (mumfordTateHopfIdeal (baseChangeMap (K := ℝ) e.hom ≫ h)) ≫
        (mumfordTateQuotientIsoOfIso e h).hom =
      e.hom ≫ mkQuotient L (mumfordTateHopfIdeal h) :=
  mkQuotient_comp_quotientIsoOfComapEq_hom _ _ _

/-- The inverse of the isomorphism of Mumford–Tate groups induced by `e` commutes with their
embeddings into the ambient groups. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_mumfordTateQuotientIsoOfIso_inv (e : H ≅ L)
    (h : baseChange (K := ℝ) L ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    mkQuotient L (mumfordTateHopfIdeal h) ≫ (mumfordTateQuotientIsoOfIso e h).inv =
      e.inv ≫ mkQuotient H (mumfordTateHopfIdeal (baseChangeMap (K := ℝ) e.hom ≫ h)) :=
  mkQuotient_comp_quotientIsoOfComapEq_inv _ _ _

/-- **Finiteness of the Mumford–Tate group.** For a noetherian coordinate Hopf algebra `H`, for
instance `H = O(GL(V))`, the Mumford–Tate ideal of `h` is the supremum of finitely many Hopf
ideals whose real extensions `h` kills: `MT(h)` is the intersection of finitely many closed
`ℚ`-subgroups through whose real extensions `h` factors. -/
theorem exists_finset_sup_eq_mumfordTateHopfIdeal [IsNoetherianRing H]
    (h : baseChange (K := ℝ) H ⟶ _root_.CommHopfAlgCat.of ℝ S) :
    ∃ t : Finset (HopfIdeal ℚ H),
      (∀ I ∈ t, (baseChangeHopfIdeal (K := ℝ) I).toIdeal ≤
        RingHom.ker h.hom.toAlgHom.toRingHom) ∧
      t.sup id = mumfordTateHopfIdeal h := by
  obtain ⟨t, ht, hsup⟩ := exists_finset_sup_eq_contractHopfIdeal (K := ℝ)
    (commonKernelHopfIdeal fun _ : Unit ↦ h)
  exact ⟨t, fun I hI ↦ (le_commonKernelHopfIdeal_iff _ _).mp (ht I hI) (), hsup⟩

end TauCeti.DeligneTorus
