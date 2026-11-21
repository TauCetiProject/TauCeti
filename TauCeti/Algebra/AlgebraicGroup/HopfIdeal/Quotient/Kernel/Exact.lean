/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Coinvariants
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.BaseChange
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion
import TauCeti.Algebra.AlgebraicGroup.Hopf.KernelPoints
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Finiteness
import TauCeti.RingTheory.Flat.Descent
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Short exact sequences of affine groups

A sequence of affine groups `1 → N → G → Q → 1` is **exact** when `G → Q` is faithfully flat (a
quotient map) and `N → G` is a closed immersion identifying `N` with the scheme-theoretic kernel
of `G → Q` (Milne, *Algebraic Groups*, §5.c). In coordinate Hopf algebras the arrows reverse:
such a sequence is a pair of morphisms

```text
O(Q) --p--> O(G) --i--> O(N)
```

of commutative Hopf algebras with `p` faithfully flat, `i` surjective, and `ker i` equal to the
kernel Hopf ideal `O(G) · p(O(Q)⁺)`. This file records that notion,
`TauCeti.CommHopfAlgCat.IsShortExact`, over an arbitrary commutative base ring, with no
smoothness, reducedness or finite-type hypotheses, and derives its basic consequences.

* Up to isomorphism, the closed subgroup in a short exact sequence is the scheme-theoretic kernel:
  `p` together with the quotient map by `kernelHopfIdeal p` is short exact, and every short exact
  sequence is isomorphic to this one (`isShortExact_iff_exists_iso`).
* The quotient is recovered from the subgroup: the functions on `G` invariant under `N` are
  exactly the functions pulled back from `Q` (`IsShortExact.coinvariants_eq_range`).
* On `A`-points, for every commutative `R`-algebra `A`, the sequence
  `N(A) → G(A) → Q(A)` is exact at `G(A)` (`IsShortExact.ker_mapPointsFunctor_app_eq_range`),
  and `N(A) → G(A)` is injective
    (`CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective`). In general
  `G(A) → Q(A)` is surjective only after a faithfully flat extension of `A`; it is surjective when
  `A` is an algebraically closed field and `p` is of finite type
  (`mapPointsFunctor_app_surjective_of_faithfullyFlat`).
* The quotient map is an isogeny exactly when the subgroup is finite
  (`IsShortExact.isIsogeny_iff_moduleFinite`).
* When `G` is finite projective over the base and `Q` is of finite type, the quotient map
  `G → Q` is finite locally free (`IsShortExact.moduleProjective`).
* Short exact sequences are stable under arbitrary base change (`IsShortExact.baseChange`), and
  short exactness descends along a faithfully flat one (`isShortExact_baseChangeMap_iff`): the
  proof descends faithful flatness, surjectivity and the equality of kernel Hopf ideals, so it
  keeps the full scheme-theoretic kernel and needs neither smoothness nor finite type. Over a
  field, exactness can thus be checked after any field extension, such as an algebraic closure.
* Short exactness is invariant under bialgebra equivalences of the three coordinate algebras
  intertwining two sequences, also across universes (`isShortExact_iff_of_bialgEquiv`), and in
  particular under isomorphisms of the coordinate algebras (`isShortExact_iso_iff`).

## Main declarations

* `TauCeti.CommHopfAlgCat.IsShortExact`: short exactness of `O(Q) ⟶ O(G) ⟶ O(N)`.
* `TauCeti.CommHopfAlgCat.IsShortExact.comp_eq_unit_comp_counit`: the composite `N → Q` is
  trivial.
* `TauCeti.CommHopfAlgCat.IsShortExact.kernelIso`: the identification of `N` with the kernel.
* `TauCeti.CommHopfAlgCat.isShortExact_mkQuotient_kernelHopfIdeal`: the canonical short exact
  sequence of a faithfully flat morphism.
* `TauCeti.CommHopfAlgCat.isShortExact_iff_exists_iso`: short exact sequences are, up to
  isomorphism, the canonical ones.
* `TauCeti.CommHopfAlgCat.IsShortExact.coinvariants_eq_range`: `O(Q) = O(G)^N`.
* `TauCeti.CommHopfAlgCat.IsShortExact.ker_mapPointsFunctor_app_eq_range`: exactness on points.
* `TauCeti.CommHopfAlgCat.IsShortExact.isIsogeny_iff_moduleFinite`: finite kernels and isogenies.
* `TauCeti.CommHopfAlgCat.IsShortExact.moduleProjective`: the quotient map of finite projective
  groups is finite locally free.
* `TauCeti.CommHopfAlgCat.IsShortExact.baseChange`: base change of short exact sequences.
* `TauCeti.CommHopfAlgCat.isShortExact_iff_of_bialgEquiv`: invariance under bialgebra equivalences
  of the coordinate algebras.
* `TauCeti.CommHopfAlgCat.isShortExact_iso_iff`: invariance under coordinate isomorphisms.
* `TauCeti.CommHopfAlgCat.isShortExact_baseChangeMap_iff`: faithfully flat descent of short exact
  sequences.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c, exact sequences of algebraic groups.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15--16.
-/

public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} [CommRing R] {Q G N : _root_.CommHopfAlgCat.{v} R}

/-- Coordinate morphisms `p : O(Q) ⟶ O(G)` and `i : O(G) ⟶ O(N)` form a **short exact
sequence** of affine groups `1 → N → G → Q → 1` when `G → Q` is faithfully flat, `N → G` is a
closed immersion, and `N` is the scheme-theoretic kernel of `G → Q`: the ideal cutting out `N`
is the kernel Hopf ideal of `p`. -/
structure IsShortExact (p : Q ⟶ G) (i : G ⟶ N) : Prop where
  /-- The quotient map `G → Q` is faithfully flat. -/
  faithfullyFlat : p.hom.toAlgHom.toRingHom.FaithfullyFlat
  /-- The map `N → G` is a closed immersion. -/
  surjective : Function.Surjective i.hom
  /-- The closed subgroup `N` of `G` is the kernel of `G → Q`. -/
  ker_eq : RingHom.ker i.hom.toAlgHom.toRingHom = (kernelHopfIdeal p).toIdeal

namespace IsShortExact

variable {p : Q ⟶ G} {i : G ⟶ N}

/-- In a short exact sequence, the Hopf ideal cutting out the subgroup is the kernel Hopf ideal
of the quotient map. -/
theorem kerOfSurjective_eq_kernelHopfIdeal (h : IsShortExact p i) :
    HopfIdeal.kerOfSurjective i.hom h.surjective = kernelHopfIdeal p := by
  ext x
  rw [HopfIdeal.mem_kerOfSurjective, ← HopfIdeal.mem_toIdeal, ← h.ker_eq, RingHom.mem_ker,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom]

/-- The composite `N → G → Q` of a short exact sequence is the trivial homomorphism. -/
@[reassoc (attr := simp)]
theorem comp_eq_unit_comp_counit (h : IsShortExact p i) :
    p ≫ i = _root_.CommHopfAlgCat.ofHom
      ((Bialgebra.unitBialgHom R N).comp (Bialgebra.counitBialgHom R Q)) :=
  (comp_eq_unit_comp_counit_iff p i).mpr h.ker_eq.ge

/-- The subgroup in a short exact sequence is isomorphic to the scheme-theoretic kernel of the
quotient map, compatibly with the inclusions into `G` (`mkQuotient_comp_kernelIso_hom`). -/
noncomputable def kernelIso (h : IsShortExact p i) : quotient G (kernelHopfIdeal p) ≅ N :=
  quotientIsoOfKerOfSurjectiveEq i h.surjective h.kerOfSurjective_eq_kernelHopfIdeal

/-- The identification of the subgroup with the kernel respects the inclusions into `G`. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_kernelIso_hom (h : IsShortExact p i) :
    mkQuotient G (kernelHopfIdeal p) ≫ h.kernelIso.hom = i :=
  mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom i h.surjective
    h.kerOfSurjective_eq_kernelHopfIdeal

/-- The inverse identification of the subgroup with the kernel respects the inclusions into
`G`. -/
@[reassoc (attr := simp)]
theorem comp_kernelIso_inv (h : IsShortExact p i) :
    i ≫ h.kernelIso.inv = mkQuotient G (kernelHopfIdeal p) :=
  comp_quotientIsoOfKerOfSurjectiveEq_inv i h.surjective h.kerOfSurjective_eq_kernelHopfIdeal

/-- The functions on `G` invariant under the subgroup `N` of a short exact sequence are exactly
the functions pulled back from the quotient `Q`. -/
theorem coinvariants_eq_range (h : IsShortExact p i) :
    (HopfIdeal.kerOfSurjective i.hom h.surjective).coinvariants = p.hom.toAlgHom.range := by
  rw [h.kerOfSurjective_eq_kernelHopfIdeal]
  exact coinvariants_kernelHopfIdeal_eq_range p h.faithfullyFlat

/-- Exactness on points: for every commutative `R`-algebra `A`, an `A`-point of `G` maps to the
identity of `Q(A)` exactly when it comes from an `A`-point of `N`. -/
theorem ker_mapPointsFunctor_app_eq_range (h : IsShortExact p i) (A : CommAlgCat.{w} R) :
    ((CommHopfAlgCat.Hom.mapPointsFunctor p).app A).hom.ker =
      ((CommHopfAlgCat.Hom.mapPointsFunctor i).app A).hom.range := by
  rw [← HopfIdeal.quotientPointsSubgroup_kerOfSurjective_eq_range_mapPointsFunctor i h.surjective A,
    h.kerOfSurjective_eq_kernelHopfIdeal,
    quotientPointsSubgroup_kernelHopfIdeal_eq_ker_mapPointsFunctor]

/-- The quotient map of a short exact sequence is an isogeny exactly when the subgroup is
finite over the base. -/
theorem isIsogeny_iff_moduleFinite (h : IsShortExact p i) : IsIsogeny p ↔ Module.Finite R N := by
  rw [CommHopfAlgCat.isIsogeny_iff, and_iff_left h.faithfullyFlat,
    finite_iff_moduleFinite_quotient_kernelHopfIdeal p h.faithfullyFlat]
  let e := (CommHopfAlgCat.ofIso h.kernelIso).toAlgEquiv.toLinearEquiv
  exact ⟨fun _ ↦ Module.Finite.equiv e, fun _ ↦ Module.Finite.equiv e.symm⟩

/-- The quotient map `G → Q` of a short exact sequence is finite locally free when `G` is finite
projective over the base and `Q` is of finite type: `O(G)` is a projective `O(Q)`-module. -/
theorem moduleProjective [Algebra.FiniteType R Q] [Module.Projective R G] [Module.Finite R G]
    (h : IsShortExact p i) :
    letI := p.hom.toAlgHom.toAlgebra
    Module.Projective Q G := by
  let := p.hom.toAlgHom.toAlgebra
  have : IsScalarTower R Q G :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (p.hom.toAlgHom.commutes r).symm
  have : Module.Finite Q G := Module.Finite.of_restrictScalars_finite R Q G
  have : Module.Flat Q G := h.faithfullyFlat.flat
  have : Module.FinitePresentation R G := Module.finitePresentation_of_projective R G
  have : Algebra.FinitePresentation Q G :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R Q G
  have : Module.FinitePresentation Q G :=
    Module.FinitePresentation.of_finite_of_finitePresentation Q G
  exact Module.Flat.projective_of_finitePresentation

/-- A short exact sequence of affine groups `1 → N → G → Q → 1` remains short exact after an
arbitrary base change `R → T`. -/
theorem baseChange (h : IsShortExact p i) (T : Type w) [CommRing T] [Algebra R T] :
    IsShortExact (baseChangeMap (K := T) p) (baseChangeMap (K := T) i) := by
  -- Elaborating the three fields against the expected structure type unfolds the base changes
  -- too eagerly; stating them first keeps unification cheap.
  have hp := RingHom.FaithfullyFlat.lTensor (S := T) T h.faithfullyFlat
  have hi := baseChangeMap_surjective (K := T) i h.surjective
  have hker : RingHom.ker (baseChangeMap (K := T) i).hom.toAlgHom.toRingHom =
      (kernelHopfIdeal (baseChangeMap (K := T) p)).toIdeal := by
    rw [← baseChangeHopfIdeal_kernelHopfIdeal, baseChangeHopfIdeal_toIdeal, ← h.ker_eq]
    exact Algebra.TensorProduct.lTensor_ker (A := T) i.hom.toAlgHom h.surjective
  exact ⟨hp, hi, hker⟩

end IsShortExact

/-- Faithfully flat scalar extension preserves and reflects short exact sequences of affine
group schemes. Over a field this applies to every field extension, including algebraic closure. -/
@[simp]
theorem isShortExact_baseChangeMap_iff {S : Type w} [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] (p : Q ⟶ G) (i : G ⟶ N) :
    IsShortExact (baseChangeMap (K := S) p) (baseChangeMap (K := S) i) ↔ IsShortExact p i := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.baseChange S⟩
  -- Faithful flatness: the algebra map underlying `baseChangeMap p` is `id ⊗ p`.
  have hp := h.faithfullyFlat
  rw [hom_baseChangeMap, Bialgebra.TensorProduct.map_toAlgHom, BialgHom.id_toAlgHom] at hp
  -- Surjectivity: the `R`-linear map underlying `baseChangeMap i` is `LinearMap.lTensor S i`.
  have hmap : (i.hom : G →ₗ[R] N).lTensor S =
      ((baseChangeMap (K := S) i).hom :
        baseChange (K := S) G →ₗ[S] baseChange (K := S) N).restrictScalars R :=
    TensorProduct.ext' fun s g ↦ by simp
  have hi : Function.Surjective i.hom := by
    rw [← BialgHom.coe_toLinearMap, ← Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S,
      hmap, LinearMap.coe_restrictScalars, BialgHom.coe_toLinearMap]
    exact h.surjective
  -- Kernel: both Hopf ideals have the same base change, the kernel of `baseChangeMap i`. The
  -- identity isomorphisms specialize `map_baseChangeHopfIdeal_kerOfSurjective` to `S ⊗[R] G`
  -- itself, where the bialgebra map of the identity morphism is `BialgHom.id` by definition.
  have heq : HopfIdeal.kerOfSurjective i.hom hi = kernelHopfIdeal p :=
    baseChangeHopfIdeal_injective (K := S) <| (HopfIdeal.map_id _).symm.trans <|
      (map_baseChangeHopfIdeal_kerOfSurjective (Iso.refl _) (Iso.refl _) hi h.surjective
        (by simp)).trans <|
      h.kerOfSurjective_eq_kernelHopfIdeal.trans (baseChangeHopfIdeal_kernelHopfIdeal p).symm
  refine ⟨.of_lTensor S hp, hi, ?_⟩
  simp [← heq, RingHom.ker_coe_toRingHom]

/-- A faithfully flat morphism and the quotient map onto its scheme-theoretic kernel form a
short exact sequence. -/
theorem isShortExact_mkQuotient_kernelHopfIdeal (p : Q ⟶ G)
    (hp : p.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    IsShortExact p (mkQuotient G (kernelHopfIdeal p)) :=
  ⟨hp, mkQuotient_surjective G _, mkQuotient_ker G _⟩

/-- A pair of coordinate morphisms is short exact exactly when the first is faithfully flat and
the second is, up to isomorphism of its target, the quotient map onto the kernel Hopf ideal of
the first. -/
theorem isShortExact_iff_exists_iso (p : Q ⟶ G) (i : G ⟶ N) :
    IsShortExact p i ↔ p.hom.toAlgHom.toRingHom.FaithfullyFlat ∧
      ∃ e : quotient G (kernelHopfIdeal p) ≅ N, mkQuotient G (kernelHopfIdeal p) ≫ e.hom = i := by
  refine ⟨fun h ↦ ⟨h.faithfullyFlat, h.kernelIso, h.mkQuotient_comp_kernelIso_hom⟩, ?_⟩
  rintro ⟨hp, e, rfl⟩
  have he := ConcreteCategory.bijective_of_isIso e.hom
  refine ⟨hp, ?_, ?_⟩
  · rw [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
    exact he.2.comp (mkQuotient_surjective G _)
  · ext x
    rw [← mkQuotient_ker G, RingHom.mem_ker, RingHom.mem_ker, _root_.CommHopfAlgCat.hom_comp,
      BialgHom.comp_toAlgHom, AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      RingHom.coe_coe, AlgHom.comp_apply]
    exact map_eq_zero_iff _ he.1

section BialgEquiv

variable {Q' G' N' : _root_.CommHopfAlgCat.{w} R}
variable {p : Q ⟶ G} {i : G ⟶ N} {p' : Q' ⟶ G'} {i' : G' ⟶ N'}

/-- Short exactness transfers along bialgebra equivalences of the three coordinate algebras
intertwining the two sequences. The two sequences may live in different universes. -/
theorem IsShortExact.of_bialgEquiv (h : IsShortExact p i)
    (eQ : Q ≃ₐc[R] Q') (eG : G ≃ₐc[R] G') (eN : N ≃ₐc[R] N')
    (hp : p'.hom.comp (eQ : Q →ₐc[R] Q') = (eG : G →ₐc[R] G').comp p.hom)
    (hi : i'.hom.comp (eG : G →ₐc[R] G') = (eN : N →ₐc[R] N').comp i.hom) :
    IsShortExact p' i' := by
  have hp' (x : Q) : p'.hom (eQ x) = eG (p.hom x) := DFunLike.congr_fun hp x
  have hi' (x : G) : i'.hom (eG x) = eN (i.hom x) := DFunLike.congr_fun hi x
  refine ⟨?_, ?_, ?_⟩
  · have hcomp : p'.hom.toAlgHom.toRingHom =
        ((eG : G →+* G').comp p.hom.toAlgHom.toRingHom).comp (eQ.symm : Q' →+* Q) := by
      ext x
      simpa using hp' (eQ.symm x)
    rw [hcomp]
    exact (RingHom.FaithfullyFlat.of_bijective eQ.symm.bijective).comp
      (h.faithfullyFlat.comp (RingHom.FaithfullyFlat.of_bijective eG.bijective))
  · intro y
    obtain ⟨y, rfl⟩ := eN.surjective y
    obtain ⟨x, rfl⟩ := h.surjective y
    exact ⟨eG x, hi' x⟩
  · have haug : (HopfIdeal.augmentation R Q').toIdeal =
        Ideal.map (eQ : Q →+* Q') (HopfIdeal.augmentation R Q).toIdeal := by
      refine (Ideal.map_comap_of_surjective (eQ : Q →+* Q') eQ.surjective _).symm.trans ?_
      congr 1
      ext x
      simp [CoalgHomClass.counit_comp_apply]
    have hmap : (kernelHopfIdeal p').toIdeal =
        Ideal.map (eG : G →+* G') (kernelHopfIdeal p).toIdeal := by
      rw [kernelHopfIdeal_toIdeal, kernelHopfIdeal_toIdeal, haug, Ideal.map_map, Ideal.map_map]
      congr 1
      ext x
      exact hp' x
    ext x
    obtain ⟨x, rfl⟩ := EquivLike.surjective eG x
    rw [hmap, Ideal.mem_map_iff_of_surjective (eG : G →+* G') eG.surjective, ← h.ker_eq]
    simp [hi']

/-- Short exactness can be checked after replacing the three coordinate algebras along
bialgebra equivalences intertwining the two sequences, possibly in another universe. -/
theorem isShortExact_iff_of_bialgEquiv
    (eQ : Q ≃ₐc[R] Q') (eG : G ≃ₐc[R] G') (eN : N ≃ₐc[R] N')
    (hp : p'.hom.comp (eQ : Q →ₐc[R] Q') = (eG : G →ₐc[R] G').comp p.hom)
    (hi : i'.hom.comp (eG : G →ₐc[R] G') = (eN : N →ₐc[R] N').comp i.hom) :
    IsShortExact p i ↔ IsShortExact p' i' := by
  refine ⟨fun h ↦ h.of_bialgEquiv eQ eG eN hp hi,
    fun h ↦ h.of_bialgEquiv eQ.symm eG.symm eN.symm ?_ ?_⟩
  · refine BialgHom.ext fun x ↦ ?_
    simp [show p'.hom x = eG (p.hom (eQ.symm x)) by
      simpa using DFunLike.congr_fun hp (eQ.symm x)]
  · refine BialgHom.ext fun x ↦ ?_
    simp [show i'.hom x = eN (i.hom (eG.symm x)) by
      simpa using DFunLike.congr_fun hi (eG.symm x)]

end BialgEquiv

section Iso

variable {Q' G' N' : _root_.CommHopfAlgCat.{v} R} {p : Q ⟶ G} {i : G ⟶ N}

/-- Short exactness can be checked after changing all three coordinate algebras by
isomorphisms. -/
@[simp]
theorem isShortExact_iso_iff (eQ : Q ≅ Q') (eG : G ≅ G') (eN : N ≅ N') :
    IsShortExact (eQ.inv ≫ p ≫ eG.hom) (eG.inv ≫ i ≫ eN.hom) ↔ IsShortExact p i :=
  (isShortExact_iff_of_bialgEquiv (ofIso eQ) (ofIso eG) (ofIso eN)
    (BialgHom.ext fun x ↦ by simp [ofIso_apply]) (BialgHom.ext fun x ↦ by simp [ofIso_apply])).symm

/-- Short exactness is preserved when the three coordinate algebras are replaced by
isomorphic ones. -/
theorem IsShortExact.of_iso (h : IsShortExact p i)
    (eQ : Q ≅ Q') (eG : G ≅ G') (eN : N ≅ N') :
    IsShortExact (eQ.inv ≫ p ≫ eG.hom) (eG.inv ≫ i ≫ eN.hom) :=
  (isShortExact_iso_iff eQ eG eN).mpr h

end Iso

end TauCeti.CommHopfAlgCat
