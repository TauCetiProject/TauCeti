/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

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
* `LinearMap.mappingCone`: the mapping cone `(m, n) ↦ (-d m, f m + e n)` of such a chain map.

## Main results

* `LinearMap.mem_boundariesInKer`: an element of the kernel is a boundary exactly when it lies in
  the image of `d`.
* `LinearMap.range_moduleCatToCycles_eq_boundariesInKer`: for `d ∘ d = 0`, the boundaries used by
  Mathlib's explicit homology of a short complex of modules are `d.boundariesInKer`.
* `LinearMap.homologyMap_surjective_iff` and `LinearMap.homologyMap_injective_iff`: elementwise
  descriptions of surjectivity and injectivity of the map induced on homology.
* `LinearMap.ker_le_range_mappingCone_iff`: a chain map induces a bijection on homology exactly when
  its mapping cone is exact.
-/

public section

open CategoryTheory

namespace LinearMap

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M] (d : M →ₗ[S] M)

/-- The intersection of the image and kernel of a linear endomorphism `d`, viewed as a submodule
of the kernel. For a square-zero endomorphism, this is its full image. -/
abbrev boundariesInKer : Submodule S (ker d) :=
  (range d).comap (ker d).subtype

/-- An element of the kernel of `d` is a boundary exactly when it is a value of `d`. -/
theorem mem_boundariesInKer {z : ker d} : z ∈ d.boundariesInKer ↔ (z : M) ∈ range d :=
  Iff.rfl

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

section Map

variable {N : Type*} [AddCommGroup N] [Module S N] {d} {e : N →ₗ[S] N}

/-- A chain map `f`, one with `f ∘ d = e ∘ f`, sends the kernel of `d` into the kernel of `e`. -/
theorem map_mem_ker_of_comp_eq (f : M →ₗ[S] N) (hf : f ∘ₗ d = e ∘ₗ f) {x : M}
    (hx : x ∈ ker d) :
    f x ∈ ker e := by
  rw [mem_ker, ← comp_apply e f, ← hf, comp_apply, mem_ker.mp hx, map_zero]

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
  apply LinearMap.ext
  intro c
  obtain ⟨z, rfl⟩ := d.homologyπ_surjective hd c
  rw [homologyπ_apply, homologyMap_mk]
  rfl

variable (d e) in
/-- The zero chain map induces the zero map on homology. -/
@[simp]
theorem homologyMap_zero (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0) :
    homologyMap (0 : M →ₗ[S] N) hd he (by simp) = 0 := by
  apply LinearMap.ext
  intro c
  obtain ⟨z, rfl⟩ := d.homologyπ_surjective hd c
  simp only [homologyπ_apply, homologyMap_mk, zero_apply]
  rfl

/-- The map on homology induced by `-f` is the negative of the map induced by `f`. -/
@[simp]
theorem homologyMap_neg (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) :
    homologyMap (-f) hd he (by rw [neg_comp, comp_neg, hf]) = -homologyMap f hd he hf := by
  apply LinearMap.ext
  intro c
  obtain ⟨z, rfl⟩ := d.homologyπ_surjective hd c
  simp only [homologyπ_apply, homologyMap_mk, neg_apply, ← Submodule.Quotient.mk_neg]
  rfl

/-- The map on homology induced by `f + g` is the sum of the maps induced by `f` and `g`. -/
@[simp]
theorem homologyMap_add (f g : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) :
    homologyMap (f + g) hd he (by rw [add_comp, comp_add, hf, hg]) =
      homologyMap f hd he hf + homologyMap g hd he hg := by
  apply LinearMap.ext
  intro c
  obtain ⟨z, rfl⟩ := d.homologyπ_surjective hd c
  simp only [homologyπ_apply, homologyMap_mk, add_apply, ← Submodule.Quotient.mk_add]
  rfl

/-- The map on homology induced by `f - g` is the difference of the maps induced by `f` and
`g`. -/
@[simp]
theorem homologyMap_sub (f g : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) (hg : g ∘ₗ d = e ∘ₗ g) :
    homologyMap (f - g) hd he (by rw [sub_comp, comp_sub, hf, hg]) =
      homologyMap f hd he hf - homologyMap g hd he hg := by
  apply LinearMap.ext
  intro c
  obtain ⟨z, rfl⟩ := d.homologyπ_surjective hd c
  simp only [homologyπ_apply, homologyMap_mk, sub_apply, ← Submodule.Quotient.mk_sub]
  rfl

variable {P : Type*} [AddCommGroup P] [Module S P] {q : P →ₗ[S] P}

/-- The map on homology induced by a composite is the composite of the induced maps. -/
theorem homologyMap_comp (g : N →ₗ[S] P) (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0)
    (he : e ∘ₗ e = 0) (hq : q ∘ₗ q = 0) (hf : f ∘ₗ d = e ∘ₗ f)
    (hg : g ∘ₗ e = q ∘ₗ g) :
    homologyMap (g ∘ₗ f) hd hq (by rw [comp_assoc, hf, ← comp_assoc, hg, comp_assoc]) =
      homologyMap g he hq hg ∘ₗ homologyMap f hd he hf := by
  apply LinearMap.ext
  intro c
  obtain ⟨z, rfl⟩ := d.homologyπ_surjective hd c
  simp only [homologyπ_apply, homologyMap_mk, comp_apply]

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
  constructor
  · intro h n hn
    obtain ⟨c, hc⟩ := h (e.homologyπ he ⟨n, hn⟩)
    obtain ⟨m, rfl⟩ := d.homologyπ_surjective hd c
    rw [homologyπ_apply, homologyMap_mk, homologyπ_apply, Submodule.Quotient.eq] at hc
    refine ⟨m, m.2, ?_⟩
    rw [← neg_mem_iff, neg_sub]
    exact hc
  · intro h c
    obtain ⟨n, rfl⟩ := e.homologyπ_surjective he c
    obtain ⟨m, hm, hnm⟩ := h n n.2
    refine ⟨d.homologyπ hd ⟨m, hm⟩, ?_⟩
    rw [homologyπ_apply, homologyMap_mk, homologyπ_apply, Submodule.Quotient.eq]
    rw [← neg_mem_iff, neg_sub] at hnm
    exact hnm

/-- The map induced by `f` on homology is injective exactly when every cycle of `d` whose image
under `f` is a boundary is itself a boundary. -/
theorem homologyMap_injective_iff (f : M →ₗ[S] N) (hd : d ∘ₗ d = 0) (he : e ∘ₗ e = 0)
    (hf : f ∘ₗ d = e ∘ₗ f) :
    Function.Injective (homologyMap f hd he hf) ↔
      ∀ m ∈ ker d, f m ∈ range e → m ∈ range d := by
  rw [← ker_eq_bot, Submodule.eq_bot_iff]
  constructor
  · intro h m hm hfm
    have := h (d.homologyπ hd ⟨m, hm⟩) <| by
      rw [mem_ker, homologyπ_apply, homologyMap_mk, ← homologyπ_apply, homologyπ_eq_zero_iff]
      exact hfm
    rwa [homologyπ_eq_zero_iff] at this
  · intro h c hc
    obtain ⟨m, rfl⟩ := d.homologyπ_surjective hd c
    rw [mem_ker, homologyπ_apply, homologyMap_mk, ← homologyπ_apply, homologyπ_eq_zero_iff] at hc
    rw [homologyπ_eq_zero_iff]
    exact h m m.2 hc

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
  · have hfd : f (d x.1) = e (f x.1) := congr($hf x.1)
    simpa [hfd] using congr($he x.2)

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

end Map

end LinearMap
