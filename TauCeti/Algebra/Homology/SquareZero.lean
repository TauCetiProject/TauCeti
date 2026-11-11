/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Module.Submodule.Ker
public import TauCeti.LinearAlgebra.Quotient.Prod

/-!
# The homology of a square-zero linear endomorphism

A linear endomorphism `d` of a module `M` with `d ∘ d = 0` is a differential module, and its
homology is the kernel of `d` modulo its image. This file names that quotient concretely as
`d.homology hd = ker d ⧸ im d`, where `hd : d ∘ₗ d = 0`, and identifies it with Mathlib's
categorical homology of the
short complex `M ⟶ M ⟶ M` whose two maps are `d` (`LinearMap.homologyIso`).

The concrete quotient is what one needs to transport extra structure to homology that the category
of modules over the ring of `d` does not see, for instance an internal grading over a smaller
coefficient ring by which `d` is homogeneous: the elements of `d.homology hd` are classes of
elements of `M`, on which such structure is defined. The image is represented inside the kernel by
`boundariesInKer`.

## Main definitions

* `LinearMap.boundariesInKer`: the image of `d` as a submodule of the kernel of `d`.
* `LinearMap.homology`: for square-zero `d`, the kernel of `d` modulo its image.
* `LinearMap.homologyπ`: the class of an element of the kernel.
* `LinearMap.homologyIso`: for `d ∘ d = 0`, Mathlib's homology of the short complex with both maps
  `d` is `d.homology hd`.
* `LinearMap.homologyMap`: the map on homology induced by a chain map `f` with `f ∘ d = e ∘ f`.
* `LinearEquiv.homologyEquiv`: the equivalence of homologies induced by a linear equivalence `f`
  with `f ∘ d = e ∘ f`.
* `LinearMap.mappingCone`: the mapping cone `(m, n) ↦ (-d m, f m + e n)` of such a chain map.
* `LinearMap.sumMappingCone`: the mapping cone of a map between free modules `ι →₀ S` and
  `κ →₀ S`, as an endomorphism of the free module `(ι ⊕ κ) →₀ S`.

## Main results

* `LinearMap.mem_boundariesInKer`: an element of the kernel is a boundary exactly when it lies in
  the image of `d`.
* `LinearMap.range_moduleCatToCycles_eq_boundariesInKer`: for `d ∘ d = 0`, the boundaries used by
  Mathlib's explicit homology of a short complex of modules are `d.boundariesInKer`.
* `LinearMap.homologyMap_surjective_iff` and `LinearMap.homologyMap_injective_iff`: elementwise
  descriptions of surjectivity and injectivity of the map induced on homology.
* `LinearMap.ker_le_range_mappingCone_iff`: a chain map induces a bijection on homology exactly when
  its mapping cone is exact.
* `LinearMap.ker_le_range_sumMappingCone_iff`: the kernel of the mapping cone on `(ι ⊕ κ) →₀ S` lies
  in its range exactly when the same holds for the mapping cone on `(ι →₀ S) × (κ →₀ S)`.
* `HomologicalComplex.quasiIso_iff_bijective_homologyMap`: a morphism of complexes of modules of
  shape `ComplexShape.refl Unit`, that is, of modules with a square-zero endomorphism, is a
  quasi-isomorphism exactly when it induces a bijection on `ker d ⧸ im d`.
* `HomologicalComplex.moduleCatHomologyIso`: the categorical homology of a one-object complex is
  the concrete homology of its differential, preserving its selected module structures.
-/

public section

open CategoryTheory

namespace LinearMap

section Semiring

variable {S M : Type*} [Semiring S] [AddCommMonoid M] [Module S M] (d : M →ₗ[S] M)

/-- The intersection of the image and kernel of a linear endomorphism `d`, viewed as a submodule
of the kernel. For a square-zero endomorphism, this is its full image. -/
abbrev boundariesInKer : Submodule S (ker d) :=
  (range d).comap (ker d).subtype

/-- An element of the kernel of `d` is a boundary exactly when it is a value of `d`. -/
theorem mem_boundariesInKer {z : ker d} : z ∈ d.boundariesInKer ↔ (z : M) ∈ range d :=
  Iff.rfl

end Semiring

section Ring

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M] (d : M →ₗ[S] M)

/-- The homology `ker d ⧸ im d` of a square-zero linear endomorphism `d`. -/
abbrev homology (_hd : d ∘ₗ d = 0) : Type _ :=
  ker d ⧸ d.boundariesInKer

/-- The class in the homology of `d` of an element of the kernel of `d`. -/
noncomputable def homologyπ (hd : d ∘ₗ d = 0) : ker d →ₗ[S] d.homology hd :=
  d.boundariesInKer.mkQ

/-- The class of an element of the kernel is its class modulo the boundaries. -/
@[simp]
theorem homologyπ_apply (hd : d ∘ₗ d = 0) (z : ker d) :
    d.homologyπ hd z = Submodule.Quotient.mk z :=
  (rfl)

/-- Every homology class is the class of an element of the kernel. -/
theorem homologyπ_surjective (hd : d ∘ₗ d = 0) : Function.Surjective (d.homologyπ hd) :=
  Submodule.mkQ_surjective _

/-- An element of the kernel has zero class exactly when it is a value of `d`. -/
theorem homologyπ_eq_zero_iff (hd : d ∘ₗ d = 0) (z : ker d) :
    d.homologyπ hd z = 0 ↔ (z : M) ∈ range d :=
  Submodule.Quotient.mk_eq_zero _

/-- The short complex `M ⟶ M ⟶ M` of `S`-modules whose two maps are a square-zero endomorphism
`d`. -/
abbrev shortComplex (hd : d ∘ₗ d = 0) : ShortComplex (ModuleCat S) :=
  ShortComplex.mk (ModuleCat.ofHom d) (ModuleCat.ofHom d) (by
    rw [← ModuleCat.ofHom_comp, hd, ModuleCat.ofHom_zero])

/-- For a square-zero endomorphism `d`, the boundaries of Mathlib's explicit homology of the short
complex `M ⟶ M ⟶ M` with both maps `d` are the image of `d` inside its kernel. -/
theorem range_moduleCatToCycles_eq_boundariesInKer (hd : d ∘ₗ d = 0) :
    range (d.shortComplex hd).moduleCatToCycles = d.boundariesInKer := by
  ext z
  rw [mem_boundariesInKer, mem_range, mem_range]
  exact exists_congr fun _ ↦ Subtype.ext_iff

/-- For a square-zero endomorphism `d`, Mathlib's homology of the short complex `M ⟶ M ⟶ M` with
both maps `d` is the concrete homology `ker d ⧸ im d`. -/
noncomputable def homologyIso (hd : d ∘ₗ d = 0) :
    (d.shortComplex hd).homology ≅ ModuleCat.of S (d.homology hd) :=
  (d.shortComplex hd).moduleCatHomologyIso ≪≫
    (Submodule.quotEquivOfEq _ _ (d.range_moduleCatToCycles_eq_boundariesInKer hd)).toModuleIso

/-- The inverse comparison sends the quotient class of a cycle to its categorical class. -/
theorem homologyIso_inv_homologyπ (hd : d ∘ₗ d = 0) (z : ker d) :
    (d.homologyIso hd).inv (d.homologyπ hd z) =
      (d.shortComplex hd).homologyπ ((d.shortComplex hd).moduleCatCyclesIso.inv z) := by
  let e := Submodule.quotEquivOfEq _ _
    (d.range_moduleCatToCycles_eq_boundariesInKer hd)
  have he : e.symm (Submodule.Quotient.mk z) = Submodule.Quotient.mk z := by
    apply e.injective
    simp only [LinearEquiv.apply_symm_apply, e, Submodule.quotEquivOfEq_mk]
  -- Separate the inverse categorical homology comparison from the boundary-submodule change.
  change (d.shortComplex hd).moduleCatHomologyIso.inv
      (e.toModuleIso.inv (Submodule.Quotient.mk z)) = _
  rw [LinearEquiv.toModuleIso_inv]
  -- Normalize the bundled module-map application to the quotient equivalence's own carrier.
  change (d.shortComplex hd).moduleCatHomologyIso.inv
      (e.symm (Submodule.Quotient.mk z)) = _
  rw [he]
  exact (congrArg (fun f => f z) (d.shortComplex hd).moduleCatCyclesIso_inv_π).symm

section Map

variable {N : Type*} [AddCommGroup N] [Module S N] {d} {e : N →ₗ[S] N}

/-- The map on homology induced by a chain map `f` from `(M, d)` to `(N, e)`, that is, a linear
map with `f ∘ d = e ∘ f`: the class of a cycle `z` goes to the class of `f z`. -/
noncomputable def homologyMap (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) : d.homology hd →ₗ[S] e.homology he :=
  d.boundariesInKer.mapQ e.boundariesInKer
    (f.restrict fun _ ↦ map_mem_ker_of_comp_eq (d := d) (e := e) f hf) <| by
    rintro z ⟨w, hw⟩
    refine ⟨f w, ?_⟩
    rw [Submodule.subtype_apply, coe_restrict_apply, ← comp_apply e f, ← hf, comp_apply, hw,
      Submodule.subtype_apply]

/-- The induced map on homology sends the class of a cycle `z` to the class of `f z`. -/
@[simp]
theorem homologyMap_mk (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) (z : ker d) :
    homologyMap f hd he hf (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ⟨f z, map_mem_ker_of_comp_eq (d := d) (e := e) f hf z.2⟩ :=
  (rfl)

variable (d) in
/-- The identity chain map induces the identity map on homology. -/
@[simp]
theorem homologyMap_id (hd : d ∘ₗ d = 0) :
    homologyMap LinearMap.id hd hd (by simp) = LinearMap.id := by
  ext z
  simp

variable (d e) in
/-- The zero chain map induces the zero map on homology. -/
@[simp]
theorem homologyMap_zero (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0) :
    homologyMap (0 : M →ₗ[S] N) hd he (by simp) = 0 := by
  ext z
  simp

/-- The map on homology induced by `-f` is the negative of the map induced by `f`. -/
@[simp]
theorem homologyMap_neg (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) :
    homologyMap (-f) hd he (by rw [neg_comp, comp_neg, hf]) = -homologyMap f hd he hf := by
  ext z
  simp [← Submodule.Quotient.mk_neg, Submodule.Quotient.eq]

/-- The map on homology induced by `f + g` is the sum of the maps induced by `f` and `g`. -/
@[simp]
theorem homologyMap_add (f g : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) :
    homologyMap (f + g) hd he (by rw [add_comp, comp_add, hf, hg]) =
      homologyMap f hd he hf + homologyMap g hd he hg := by
  ext z
  simp [← Submodule.Quotient.mk_add]

/-- The map on homology induced by `f - g` is the difference of the maps induced by `f` and
`g`. -/
@[simp]
theorem homologyMap_sub (f g : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) :
    homologyMap (f - g) hd he (by rw [sub_comp, comp_sub, hf, hg]) =
      homologyMap f hd he hf - homologyMap g hd he hg := by
  ext z
  simp [← Submodule.Quotient.mk_sub, Submodule.Quotient.eq]

variable {P : Type*} [AddCommGroup P] [Module S P] {q : P →ₗ[S] P}

/-- The map on homology induced by a composite is the composite of the induced maps. -/
theorem homologyMap_comp (g : N →ₗ[S] P) (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0)
    (he : e ∘ₗ e = 0) (hq : q ∘ₗ q = 0) (hf : f ∘ₗ d = e ∘ₗ f)
    (hg : g ∘ₗ e = q ∘ₗ g) :
    homologyMap (g ∘ₗ f) hd hq (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) =
      homologyMap g he hq hg ∘ₗ homologyMap f hd he hf := by
  ext z
  simp

/-- The composite of two induced maps on homology is the map induced by the composite. This is
`homologyMap_comp` read right to left, the orientation usable by `simp`: its left-hand side
mentions the intermediate differential `e`, which the left-hand side of `homologyMap_comp` does
not. -/
@[simp]
theorem homologyMap_comp_homologyMap (g : N →ₗ[S] P) (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0)
    (he : e ∘ₗ e = 0) (hq : q ∘ₗ q = 0) (hf : f ∘ₗ d = e ∘ₗ f)
    (hg : g ∘ₗ e = q ∘ₗ g) :
    homologyMap g he hq hg ∘ₗ homologyMap f hd he hf =
      homologyMap (g ∘ₗ f) hd hq (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) :=
  (homologyMap_comp g f hd he hq hf hg).symm

/-- Applying two induced maps on homology in turn is applying the map induced by the composite. -/
@[simp]
theorem homologyMap_homologyMap (g : N →ₗ[S] P) (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0)
    (he : e ∘ₗ e = 0) (hq : q ∘ₗ q = 0) (hf : f ∘ₗ d = e ∘ₗ f)
    (hg : g ∘ₗ e = q ∘ₗ g) (c : d.homology hd) :
    homologyMap g he hq hg (homologyMap f hd he hf c) =
      homologyMap (g ∘ₗ f) hd hq (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) c :=
  congr($(homologyMap_comp_homologyMap g f hd he hq hf hg) c)

/-- The map induced by `f` on homology is surjective exactly when every cycle of `e` differs from
the image of a cycle of `d` by a boundary. -/
theorem homologyMap_surjective_iff (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) :
    Function.Surjective (homologyMap f hd he hf) ↔
      ∀ n ∈ ker e, ∃ m ∈ ker d, n - f m ∈ range e := by
  refine ⟨fun h n hn ↦ ?_, fun h c ↦ ?_⟩
  · obtain ⟨c, hc⟩ := h (e.homologyπ he ⟨n, hn⟩)
    obtain ⟨m, rfl⟩ := d.homologyπ_surjective hd c
    simp only [homologyπ_apply, homologyMap_mk, Submodule.Quotient.eq'] at hc
    exact ⟨m, m.2, by simpa [neg_add_eq_sub] using hc⟩
  · obtain ⟨n, rfl⟩ := e.homologyπ_surjective he c
    obtain ⟨m, hm, hnm⟩ := h n n.2
    refine ⟨d.homologyπ hd ⟨m, hm⟩, ?_⟩
    simpa [Submodule.Quotient.eq', neg_add_eq_sub] using hnm

/-- The map induced by `f` on homology is injective exactly when every cycle of `d` whose image
under `f` is a boundary is itself a boundary. -/
theorem homologyMap_injective_iff (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) :
    Function.Injective (homologyMap f hd he hf) ↔
      ∀ m ∈ ker d, f m ∈ range e → m ∈ range d := by
  rw [← ker_eq_bot, Submodule.eq_bot_iff]
  refine ⟨fun h m hm hfm ↦ ?_, fun h c hc ↦ ?_⟩
  · simpa [Submodule.Quotient.mk_eq_zero] using h (d.homologyπ hd ⟨m, hm⟩) <| by
      simpa [Submodule.Quotient.mk_eq_zero] using hfm
  · obtain ⟨m, rfl⟩ := d.homologyπ_surjective hd c
    simp only [mem_ker, homologyπ_apply, homologyMap_mk, Submodule.Quotient.mk_eq_zero] at hc ⊢
    exact h m m.2 hc

end Map

section Product

variable {N : Type*} [AddCommGroup N] [Module S N] (e : N →ₗ[S] N)

/-- Homology of a product differential is the product of the two homologies. -/
noncomputable def homologyProdEquiv (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0) :
    (d.prodMap e).homology (by rw [prodMap_comp, hd, he]; ext <;> simp) ≃ₗ[S]
      d.homology hd × e.homology he := by
  let E : ker (d.prodMap e) ≃ₗ[S] ker d × ker e :=
    (LinearEquiv.ofEq _ _ (ker_prodMap d e)).trans ((ker d).prodEquiv (ker e))
  refine (Submodule.Quotient.equiv (d.prodMap e).boundariesInKer
    (d.boundariesInKer.prod e.boundariesInKer) E ?_).trans
      (Submodule.quotientProdEquiv _ _)
  ext z
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨v, hv⟩ := (mem_boundariesInKer _).mp hw
    exact ⟨⟨v.1, congrArg Prod.fst hv⟩, ⟨v.2, congrArg Prod.snd hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨E.symm z, ?_, E.apply_symm_apply z⟩
    exact ⟨(u, v), Prod.ext hu hv⟩

/-- The product-homology equivalence sends a cycle class to its two component classes. -/
@[simp]
theorem homologyProdEquiv_mk (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (z : ker (d.prodMap e)) :
    d.homologyProdEquiv e hd he (Submodule.Quotient.mk z) =
      (Submodule.Quotient.mk ⟨z.1.1, congrArg Prod.fst (mem_ker.mp z.2)⟩,
        Submodule.Quotient.mk ⟨z.1.2, congrArg Prod.snd (mem_ker.mp z.2)⟩) := by
  simp [homologyProdEquiv, Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]

/-- The inverse product-homology equivalence sends two cycle classes to their product class. -/
@[simp]
theorem homologyProdEquiv_symm_mk (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (x : ker d) (y : ker e) :
    (d.homologyProdEquiv e hd he).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨((x : M), (y : N)), mem_ker.mpr (Prod.ext (mem_ker.mp x.2) (mem_ker.mp y.2))⟩ := by
  apply (d.homologyProdEquiv e hd he).injective
  simp only [LinearEquiv.apply_symm_apply, homologyProdEquiv_mk]

end Product

end Ring

section MappingCone

variable {S M N : Type*} [Semiring S] [AddCommGroup M] [Module S M] [AddCommMonoid N] [Module S N]
  {d : M →ₗ[S] M} {e : N →ₗ[S] N}

variable (d e) in
/-- The mapping cone of a linear map `f : M → N` between modules with endomorphisms `d` and `e`:
the endomorphism `(m, n) ↦ (-d m, f m + e n)` of `M × N`. It squares to zero when `d` and `e` do
and `f` is a chain map (`LinearMap.mappingCone_comp_self`). -/
def mappingCone (f : M →ₗ[S] N) : M × N →ₗ[S] M × N :=
  ((-d) ∘ₗ fst S M N).prod (f.coprod e)

/-- The mapping cone sends `(m, n)` to `(-d m, f m + e n)`. -/
@[simp]
theorem mappingCone_apply (f : M →ₗ[S] N) (x : M × N) :
    mappingCone d e f x = (-d x.1, f x.1 + e x.2) :=
  (rfl)

/-- The mapping cone of a chain map between square-zero endomorphisms squares to zero. -/
theorem mappingCone_comp_self (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) : mappingCone d e f ∘ₗ mappingCone d e f = 0 := by
  refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
  · simpa using congr($hd x.1)
  · have hfd : e (f x.1) = f (d x.1) := (congr($hf x.1)).symm
    have he2 : e (e x.2) = 0 := by simpa using congr($he x.2)
    calc
      ((mappingCone d e f ∘ₗ mappingCone d e f) x).2
        = f (-d x.1) + (e (f x.1) + e (e x.2)) := by
          simp only [comp_apply, mappingCone_apply, map_add]
      _ = (f (-d x.1) + f (d x.1)) + e (e x.2) := by
          rw [hfd, add_assoc]
      _ = f (-d x.1 + d x.1) + 0 := by
          rw [← map_add, he2]
      _ = 0 := by
          rw [neg_add_cancel, map_zero, add_zero]

end MappingCone

section Ring

variable {S M N : Type*} [Ring S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  {d : M →ₗ[S] M} {e : N →ₗ[S] N}

/-- A chain map induces a bijection on homology exactly when its mapping cone is exact, that is,
when every element killed by the mapping cone is in its image. -/
theorem ker_le_range_mappingCone_iff (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) :
    ker (mappingCone d e f) ≤ range (mappingCone d e f) ↔
      Function.Bijective (homologyMap f hd he hf) := by
  have hfd (x : M) : f (d x) = e (f x) := congr($hf x)
  rw [Function.Bijective, homologyMap_injective_iff, homologyMap_surjective_iff]
  constructor
  · intro h
    refine ⟨fun m hm ⟨n, hn⟩ ↦ ?_, fun n hn ↦ ?_⟩
    · obtain ⟨⟨a, b⟩, hab⟩ := h (x := (m, -n)) <| by
        simp [mem_ker.mp hm, hn]
      refine ⟨-a, ?_⟩
      simpa using congr($hab.1)
    · obtain ⟨⟨a, b⟩, hab⟩ := h (x := (0, n)) <| by
        simp [mem_ker.mp hn]
      have ha : d a = 0 := neg_eq_zero.mp congr($hab.1)
      refine ⟨a, ha, b, ?_⟩
      have hab2 : f a + e b = n := congr($hab.2)
      rw [← hab2]
      abel
  · rintro ⟨hinj, hsurj⟩ ⟨m, n⟩ hmn
    simp only [mem_ker, mappingCone_apply, Prod.mk_eq_zero, neg_eq_zero] at hmn
    obtain ⟨hm, hmn⟩ := hmn
    obtain ⟨a, rfl⟩ := hinj m hm ⟨-n, by rw [map_neg, ← eq_neg_of_add_eq_zero_left hmn]⟩
    have hn : n + f a ∈ ker e := by
      rw [mem_ker, map_add, ← hfd, add_comm]
      exact hmn
    obtain ⟨b, hb, c, hc⟩ := hsurj _ hn
    refine ⟨(b - a, c), ?_⟩
    simp only [mappingCone_apply, map_sub, mem_ker.mp hb, zero_sub, neg_neg, Prod.mk.injEq,
      true_and]
    rw [hc]
    abel

end Ring

/-! ### Mapping cones of maps between free modules -/

section SumMappingCone

open Finsupp

variable {S ι κ : Type*} [Ring S]

/-- The mapping cone of a map `f : (ι →₀ S) → (κ →₀ S)` between free modules with endomorphisms
`d` and `e`, as an endomorphism of the free module `(ι ⊕ κ) →₀ S` on the disjoint union of the two
bases: `LinearMap.mappingCone d e f` transported along `Finsupp.sumFinsuppLEquivProdFinsupp`. -/
noncomputable def sumMappingCone (d : (ι →₀ S) →ₗ[S] (ι →₀ S)) (e : (κ →₀ S) →ₗ[S] (κ →₀ S))
    (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) : ((ι ⊕ κ) →₀ S) →ₗ[S] ((ι ⊕ κ) →₀ S) :=
  (sumFinsuppLEquivProdFinsupp S).symm.conjRingEquiv (mappingCone d e f)

/-- The mapping cone on `(ι ⊕ κ) →₀ S` is the mapping cone on `(ι →₀ S) × (κ →₀ S)` between the
two `Finsupp` sum-product equivalences. -/
@[simp]
theorem sumMappingCone_apply (d : (ι →₀ S) →ₗ[S] (ι →₀ S)) (e : (κ →₀ S) →ₗ[S] (κ →₀ S))
    (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) (x : (ι ⊕ κ) →₀ S) :
    sumMappingCone d e f x =
      (sumFinsuppLEquivProdFinsupp S).symm (mappingCone d e f (sumFinsuppLEquivProdFinsupp S x)) :=
  (rfl)

/-- The coefficient of the mapping cone between two generators of `ι` is minus that of `d`. -/
theorem sumMappingCone_single_inl_apply_inl (d : (ι →₀ S) →ₗ[S] (ι →₀ S))
    (e : (κ →₀ S) →ₗ[S] (κ →₀ S)) (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) (i j : ι) (c : S) :
    sumMappingCone d e f (Finsupp.single (.inl i) c) (.inl j) = -d (Finsupp.single i c) j := by
  simp

/-- The coefficient of the mapping cone from a generator of `ι` to a generator of `κ` is that
of `f`. -/
theorem sumMappingCone_single_inl_apply_inr (d : (ι →₀ S) →ₗ[S] (ι →₀ S))
    (e : (κ →₀ S) →ₗ[S] (κ →₀ S)) (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) (i : ι) (k : κ) (c : S) :
    sumMappingCone d e f (Finsupp.single (.inl i) c) (.inr k) = f (Finsupp.single i c) k := by
  simp

/-- The mapping cone has no coefficient from a generator of `κ` to a generator of `ι`. -/
theorem sumMappingCone_single_inr_apply_inl (d : (ι →₀ S) →ₗ[S] (ι →₀ S))
    (e : (κ →₀ S) →ₗ[S] (κ →₀ S)) (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) (k : κ) (i : ι) (c : S) :
    sumMappingCone d e f (Finsupp.single (.inr k) c) (.inl i) = 0 := by
  simp

/-- The coefficient of the mapping cone between two generators of `κ` is that of `e`. -/
theorem sumMappingCone_single_inr_apply_inr (d : (ι →₀ S) →ₗ[S] (ι →₀ S))
    (e : (κ →₀ S) →ₗ[S] (κ →₀ S)) (f : (ι →₀ S) →ₗ[S] (κ →₀ S)) (k k' : κ) (c : S) :
    sumMappingCone d e f (Finsupp.single (.inr k) c) (.inr k') = e (Finsupp.single k c) k' := by
  simp

/-- The mapping cone on `(ι ⊕ κ) →₀ S` of a chain map between square-zero endomorphisms squares
to zero. -/
theorem sumMappingCone_comp_self {d : (ι →₀ S) →ₗ[S] (ι →₀ S)} {e : (κ →₀ S) →ₗ[S] (κ →₀ S)}
    {f : (ι →₀ S) →ₗ[S] (κ →₀ S)} (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0) (hf : f ∘ₗ d = e ∘ₗ f) :
    sumMappingCone d e f ∘ₗ sumMappingCone d e f = 0 := by
  unfold sumMappingCone
  rw [← Module.End.mul_eq_comp, ← map_mul, Module.End.mul_eq_comp,
    mappingCone_comp_self f hd he hf, map_zero]

/-- The kernel of the mapping cone on `(ι ⊕ κ) →₀ S` lies in its range exactly when the kernel of
the mapping cone on `(ι →₀ S) × (κ →₀ S)` lies in its range. -/
theorem ker_le_range_sumMappingCone_iff {d : (ι →₀ S) →ₗ[S] (ι →₀ S)}
    {e : (κ →₀ S) →ₗ[S] (κ →₀ S)} {f : (ι →₀ S) →ₗ[S] (κ →₀ S)} :
    ker (sumMappingCone d e f) ≤ range (sumMappingCone d e f) ↔
      ker (mappingCone d e f) ≤ range (mappingCone d e f) := by
  -- Rewrite the transported cone as a composition through its application rule.
  have hcomp : sumMappingCone d e f = (sumFinsuppLEquivProdFinsupp S).symm.toLinearMap ∘ₗ
      mappingCone d e f ∘ₗ (sumFinsuppLEquivProdFinsupp S).toLinearMap :=
    LinearMap.ext fun x ↦ by simp
  rw [hcomp, LinearEquiv.ker_comp, ker_comp, range_comp, LinearEquiv.range_comp,
    Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm]
  exact Submodule.comap_le_comap_iff_of_surjective (LinearEquiv.surjective _)

end SumMappingCone

end LinearMap

namespace LinearEquiv

variable {S M M' : Type*} [Ring S] [AddCommGroup M] [Module S M] [AddCommGroup M'] [Module S M']
  {d : M →ₗ[S] M} {e : M' →ₗ[S] M'}

/-- A linear equivalence `f` with `f ∘ d = e ∘ f` induces an equivalence of the homologies of the
square-zero endomorphisms `d` and `e`. -/
noncomputable def homologyEquiv (f : M ≃ₗ[S] M') (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap) : d.homology hd ≃ₗ[S] e.homology he :=
  have hf' : f.symm.toLinearMap ∘ₗ e = d ∘ₗ f.symm.toLinearMap := by
    ext m'
    apply f.injective
    simpa using (congr($hf (f.symm m'))).symm
  LinearEquiv.ofLinearMap (LinearMap.homologyMap f.toLinearMap hd he hf)
    (LinearMap.homologyMap f.symm.toLinearMap he hd hf')
    (by ext z; simp) (by ext z; simp)

/-- The equivalence of homologies sends the class of a cycle `z` to the class of `f z`. -/
@[simp]
theorem homologyEquiv_mk (f : M ≃ₗ[S] M') (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f.toLinearMap ∘ₗ d = e ∘ₗ f.toLinearMap) (z : LinearMap.ker d) :
    f.homologyEquiv hd he hf (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        ⟨f z, LinearMap.map_mem_ker_of_comp_eq (d := d) (e := e) f.toLinearMap hf z.2⟩ :=
  LinearMap.homologyMap_mk f.toLinearMap hd he hf z

end LinearEquiv

/-! ### Quasi-isomorphisms of one-object complexes -/

namespace HomologicalComplex

variable {S : Type*} [Ring S] {K L : HomologicalComplex (ModuleCat S) (ComplexShape.refl Unit)}

variable (K) in
/-- The unique differential of a complex of shape `ComplexShape.refl Unit` squares to zero, as a
linear map. -/
theorem hom_d_comp_hom_d : (K.d () ()).hom ∘ₗ (K.d () ()).hom = 0 := by
  rw [← ModuleCat.hom_comp, K.d_comp_d, ModuleCat.hom_zero]

variable (K) in
/-- The homology of a one-object complex of modules is the kernel of its differential modulo
its image, with the module structures selected by the complex. -/
noncomputable def moduleCatHomologyIso :
    K.homology () ≅ ModuleCat.of S ((K.d () ()).hom.homology K.hom_d_comp_hom_d) :=
  K.homologyIsoSc' () () () rfl rfl ≪≫ (K.d () ()).hom.homologyIso K.hom_d_comp_hom_d

variable (K) in
/-- The inverse concrete comparison sends a quotient class to the canonical categorical class. -/
theorem moduleCatHomologyIso_inv_homologyπ (z : LinearMap.ker (K.d () ()).hom) :
    K.moduleCatHomologyIso.inv ((K.d () ()).hom.homologyπ K.hom_d_comp_hom_d z) =
      K.moduleCatKerHomologyClass (rfl : (ComplexShape.refl Unit).next () = ()) z := by
  -- Expose the linear-map comparison factor so its public inverse-class equation applies.
  change (K.homologyIsoSc' () () () rfl rfl).inv
      (((K.d () ()).hom.homologyIso K.hom_d_comp_hom_d).inv
        ((K.d () ()).hom.homologyπ K.hom_d_comp_hom_d z)) = _
  rw [LinearMap.homologyIso_inv_homologyπ]
  rw [homologyIsoSc'_eq_refl]
  let y : K.cycles () := (K.sc ()).moduleCatCyclesIso.inv z
  have hy : K.moduleCatCyclesToKer () () y = z := by
    apply Subtype.ext
    rw [K.coe_moduleCatCyclesToKer]
    exact (K.sc ()).moduleCatCyclesIso_inv_iCycles_apply z
  have h := K.moduleCatKerHomologyClass_moduleCatCyclesToKer
    (rfl : (ComplexShape.refl Unit).next () = ()) y
  rw [hy] at h
  exact h.symm

variable (K) in
/-- The concrete comparison sends the canonical categorical class to its quotient class. -/
theorem moduleCatHomologyIso_hom_moduleCatKerHomologyClass
    (z : LinearMap.ker (K.d () ()).hom) :
    K.moduleCatHomologyIso.hom
        (K.moduleCatKerHomologyClass (rfl : (ComplexShape.refl Unit).next () = ()) z) =
      (K.d () ()).hom.homologyπ K.hom_d_comp_hom_d z := by
  rw [← K.moduleCatHomologyIso_inv_homologyπ, Iso.inv_hom_id_apply]

/-- The unique component of a morphism of complexes of shape `ComplexShape.refl Unit` is a chain
map in the sense of `LinearMap.homologyMap`. -/
theorem Hom.hom_f_comp_hom_d (φ : K ⟶ L) :
    (φ.f ()).hom ∘ₗ (K.d () ()).hom = (L.d () ()).hom ∘ₗ (φ.f ()).hom := by
  rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, φ.comm]

/-- **Quasi-isomorphisms of one-object complexes are detected on `ker d ⧸ im d`.** A morphism of
complexes of modules of shape `ComplexShape.refl Unit` is a quasi-isomorphism exactly when its
unique component induces a bijection between the concrete homologies `LinearMap.homology`. -/
theorem quasiIso_iff_bijective_homologyMap (φ : K ⟶ L) :
    QuasiIso φ ↔ Function.Bijective (LinearMap.homologyMap (φ.f ()).hom K.hom_d_comp_hom_d
      L.hom_d_comp_hom_d φ.hom_f_comp_hom_d) := by
  -- Compute Mathlib's homology through the explicit left homology data of modules, whose
  -- homology is `ker d` modulo the range of `d` in `ker d`, the concrete homology up to
  -- `Submodule.quotEquivOfEq`.
  rw [quasiIso_iff, Unique.forall_iff, quasiIsoAt_iff,
    ShortComplex.quasiIso_iff_isIso_leftHomologyMap' _ (K.sc ()).moduleCatLeftHomologyData
      (L.sc ()).moduleCatLeftHomologyData, ConcreteCategory.isIso_iff_bijective]
  set ψ := (shortComplexFunctor _ _ ()).map φ
  set A := ShortComplex.leftHomologyMap' ψ (K.sc ()).moduleCatLeftHomologyData
    (L.sc ()).moduleCatLeftHomologyData
  let eK := Submodule.quotEquivOfEq _ _
    ((K.d () ()).hom.range_moduleCatToCycles_eq_boundariesInKer K.hom_d_comp_hom_d)
  let eL := Submodule.quotEquivOfEq _ _
    ((L.d () ()).hom.range_moduleCatToCycles_eq_boundariesInKer L.hom_d_comp_hom_d)
  have key (z : LinearMap.ker (K.d () ()).hom) :
      eL (A.hom (Submodule.Quotient.mk z)) =
        LinearMap.homologyMap (φ.f ()).hom K.hom_d_comp_hom_d L.hom_d_comp_hom_d
          φ.hom_f_comp_hom_d (eK (Submodule.Quotient.mk z)) := by
    have hπ : A.hom (Submodule.Quotient.mk z) = Submodule.Quotient.mk ((ShortComplex.cyclesMap' ψ
        (K.sc ()).moduleCatLeftHomologyData (L.sc ()).moduleCatLeftHomologyData).hom z) :=
      congr($(ShortComplex.leftHomologyπ_naturality' ψ
        (K.sc ()).moduleCatLeftHomologyData (L.sc ()).moduleCatLeftHomologyData).hom z)
    have hi : (L.sc ()).moduleCatLeftHomologyData.i.hom ((ShortComplex.cyclesMap' ψ
        (K.sc ()).moduleCatLeftHomologyData (L.sc ()).moduleCatLeftHomologyData).hom z) =
        (φ.f ()).hom z :=
      congr($(ShortComplex.cyclesMap'_i ψ
        (K.sc ()).moduleCatLeftHomologyData (L.sc ()).moduleCatLeftHomologyData).hom z)
    have hw : (ShortComplex.cyclesMap' ψ (K.sc ()).moduleCatLeftHomologyData
        (L.sc ()).moduleCatLeftHomologyData).hom z =
        (⟨(φ.f ()).hom z, LinearMap.map_mem_ker_of_comp_eq _ φ.hom_f_comp_hom_d z.2⟩ :
          LinearMap.ker (L.d () ()).hom) :=
      Subtype.ext hi
    rw [hπ, hw]
    simp only [eK, Submodule.quotEquivOfEq_mk, LinearMap.homologyMap_mk]
    exact Submodule.quotEquivOfEq_mk _ _ _ _
  have hA : eL ∘ A.hom = LinearMap.homologyMap (φ.f ()).hom K.hom_d_comp_hom_d
      L.hom_d_comp_hom_d φ.hom_f_comp_hom_d ∘ eK := by
    funext c
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    exact key z
  rw [← EquivLike.comp_bijective (ConcreteCategory.hom A) eL, ← EquivLike.bijective_comp eK]
  exact iff_of_eq (congrArg _ hA)

end HomologicalComplex
