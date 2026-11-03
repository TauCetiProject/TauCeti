/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero

/-!
# Quotienting a differential module by a null-homotopic regular endomorphism

Let `d` be a square-zero linear endomorphism of a module `M`, and let `N` be a submodule with
`d N ⊆ N`. Then `d` induces a square-zero endomorphism of `M ⧸ N`, whose homology is written
`d.quotientHomology hd N hN`.

Suppose that `v` is an endomorphism of `M` commuting with `d` which is null-homotopic modulo `N`,
`d h + h d ≡ v (mod N)` for an endomorphism `h` with `h N ⊆ N`, and which is regular modulo `N`:
`v m ∈ N` only for `m ∈ N`. Then passing from `M ⧸ N` to `M ⧸ (N ⊔ range v)` doubles the homology:

`H(M ⧸ (N ⊔ range v)) ≅ H(M ⧸ N) × H(M ⧸ N)`,

the first factor included by the quotient map and the second by `h`
(`LinearMap.quotientHomologyProdEquiv`). This is the algebraic step behind the dependence of
fully blocked grid homology on the grid size, where `v` is multiplication by a grid variable, which
acts on the chain module freely and is null-homotopic on the simply blocked complex; it replaces
the long exact sequence of `0 → M ⧸ N → M ⧸ N → M ⧸ (N ⊔ range v) → 0`, whose connecting map is
surjective because `v` acts by zero on homology.

A surjection `π : M → M'` with kernel `N` intertwining `d` with a square-zero `d'` identifies
`d.quotientHomology hd N hN` with the homology of `d'`
(`LinearMap.quotientHomologyEquivOfSurjective`). It rests on the equivalence of homologies induced
by a linear equivalence intertwining two square-zero endomorphisms (`LinearEquiv.homologyEquiv`).

## Main definitions

* `LinearMap.quotientHomology`: the homology of the endomorphism of `M ⧸ N` induced by `d`.
* `LinearMap.quotientHomologyClass`: the class in it of an element `m` with `d m ∈ N`.
* `LinearMap.quotientHomologyEquivOfSurjective`: its identification with the homology of `d'`
  along a surjection with kernel `N`.
* `LinearMap.quotientHomologyMapOfLE`: the map `H(M ⧸ N) → H(M ⧸ N')` induced by `N ≤ N'`.
* `LinearMap.quotientHomologyProdEquiv`: the equivalence
  `H(M ⧸ N) × H(M ⧸ N) ≃ H(M ⧸ (N ⊔ range v))`.

## References

* P. Ozsváth, A. Stipsicz, Z. Szabó, *Grid Homology for Knots and Links*, AMS Mathematical Surveys
  and Monographs 208, 2015, Section 4.6, where this splitting computes fully blocked grid homology
  from simply blocked grid homology.
-/

public section

namespace Submodule

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M] {d : M →ₗ[S] M}
  {N : Submodule S M} {hN : N ≤ N.comap d}

/-- The class of `m` lies in the kernel of the endomorphism induced on `M ⧸ N` exactly when
`d m ∈ N`. -/
theorem mk_mem_ker_mapQ_iff (m : M) :
    (Quotient.mk m : M ⧸ N) ∈ LinearMap.ker (N.mapQ N d hN) ↔ d m ∈ N := by
  rw [LinearMap.mem_ker, mapQ_apply, Quotient.mk_eq_zero]

/-- The class of `m` lies in the image of the endomorphism induced on `M ⧸ N` exactly when `m`
differs from a value of `d` by an element of `N`. -/
theorem mk_mem_range_mapQ_iff (m : M) :
    (Quotient.mk m : M ⧸ N) ∈ LinearMap.range (N.mapQ N d hN) ↔ ∃ w, m - d w ∈ N := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨w, rfl⟩ := Quotient.mk_surjective N w
    rw [mapQ_apply, Quotient.eq] at hw
    exact ⟨w, sub_mem_comm_iff.mp hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨Quotient.mk w, by
      rw [mapQ_apply, Quotient.eq]
      exact sub_mem_comm_iff.mp hw⟩

end Submodule

namespace LinearMap

variable {S M : Type*} [Ring S] [AddCommGroup M] [Module S M]

section Quotient

variable (d : M →ₗ[S] M) (hd : d ∘ₗ d = 0)

/-- The endomorphism of `M ⧸ N` induced by a square-zero endomorphism `d` with `d N ⊆ N` squares to
zero. -/
theorem mapQ_comp_mapQ_eq_zero (hd : d ∘ₗ d = 0) (N : Submodule S M) (hN : N ≤ N.comap d) :
    N.mapQ N d hN ∘ₗ N.mapQ N d hN = 0 := by
  ext m
  simpa using congr(Submodule.Quotient.mk (p := N) ($hd m))

/-- The homology of the square-zero endomorphism of `M ⧸ N` induced by `d`, for a submodule `N`
with `d N ⊆ N`. -/
abbrev quotientHomology (N : Submodule S M) (hN : N ≤ N.comap d) : Type _ :=
  (N.mapQ N d hN).homology (d.mapQ_comp_mapQ_eq_zero hd N hN)

variable {d} {N : Submodule S M} {hN : N ≤ N.comap d}

variable (hN) in
/-- The class in `d.quotientHomology hd N hN` of an element `m` with `d m ∈ N`. -/
noncomputable def quotientHomologyClass (m : M) (hm : d m ∈ N) : d.quotientHomology hd N hN :=
  Submodule.Quotient.mk ⟨Submodule.Quotient.mk m, (Submodule.mk_mem_ker_mapQ_iff m).mpr hm⟩

/-- The class of `m` is the class of the cycle `Submodule.Quotient.mk m` of `M ⧸ N`. -/
@[simp]
theorem quotientHomologyClass_def (m : M) (hm : d m ∈ N) :
    quotientHomologyClass hd hN m hm =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk m, (Submodule.mk_mem_ker_mapQ_iff m).mpr hm⟩ :=
  (rfl)

/-- Every class in `d.quotientHomology hd N hN` is the class of some `m` with `d m ∈ N`. -/
theorem exists_quotientHomologyClass_eq (x : d.quotientHomology hd N hN) :
    ∃ m hm, quotientHomologyClass hd hN m hm = x := by
  obtain ⟨⟨q, hq⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
  exact ⟨m, (Submodule.mk_mem_ker_mapQ_iff m).mp hq, rfl⟩

/-- The class of `m` vanishes exactly when `m` differs from a value of `d` by an element of
`N`. -/
theorem quotientHomologyClass_eq_zero_iff (m : M) (hm : d m ∈ N) :
    quotientHomologyClass hd hN m hm = 0 ↔ ∃ w, m - d w ∈ N := by
  rw [quotientHomologyClass, Submodule.Quotient.mk_eq_zero, mem_boundariesInKer]
  exact Submodule.mk_mem_range_mapQ_iff m

/-- The class of a sum is the sum of the classes. -/
theorem quotientHomologyClass_add (m m' : M) (hm : d m ∈ N) (hm' : d m' ∈ N) :
    quotientHomologyClass hd hN m hm + quotientHomologyClass hd hN m' hm' =
      quotientHomologyClass hd hN (m + m') (by rw [map_add]; exact N.add_mem hm hm') :=
  (rfl)

end Quotient

section Transfer

variable {M' : Type*} [AddCommGroup M'] [Module S M'] {d : M →ₗ[S] M} (hd : d ∘ₗ d = 0)
  {N : Submodule S M} (hN : N ≤ N.comap d) {d' : M' →ₗ[S] M'} (hd' : d' ∘ₗ d' = 0)

/-- If `π : M → M'` is surjective with kernel `N` and `π ∘ d = d' ∘ π`, then the homology of `d`
modulo `N` is the homology of `d'`. -/
noncomputable def quotientHomologyEquivOfSurjective (π : M →ₗ[S] M') (hπ : Function.Surjective π)
    (hker : ker π = N) (hπd : π ∘ₗ d = d' ∘ₗ π) :
    d.quotientHomology hd N hN ≃ₗ[S] d'.homology hd' :=
  LinearEquiv.homologyEquiv
    ((Submodule.quotEquivOfEq N (ker π) hker.symm).trans (π.quotKerEquivOfSurjective hπ))
    _ hd' (by
      ext m
      exact congr($hπd m))

/-- The identification along `π` sends the class of `m` to the class of `π m`. -/
@[simp]
theorem quotientHomologyEquivOfSurjective_mk (π : M →ₗ[S] M') (hπ : Function.Surjective π)
    (hker : ker π = N) (hπd : π ∘ₗ d = d' ∘ₗ π) (m : M) (hm : d m ∈ N) :
    quotientHomologyEquivOfSurjective hd hN hd' π hπ hker hπd
        (Submodule.Quotient.mk
          ⟨Submodule.Quotient.mk m, (Submodule.mk_mem_ker_mapQ_iff m).mpr hm⟩) =
      Submodule.Quotient.mk ⟨π m, by
        rw [mem_ker, ← comp_apply, ← hπd, comp_apply, ← mem_ker, hker]
        exact hm⟩ := by
  simp [quotientHomologyEquivOfSurjective]

end Transfer

section OfLE

variable {d : M →ₗ[S] M} (hd : d ∘ₗ d = 0) {N N' : Submodule S M} (hN : N ≤ N.comap d)
  (hN' : N' ≤ N'.comap d) (hNN' : N ≤ N')

/-- The map `H(M ⧸ N) → H(M ⧸ N')` induced by the quotient map `M ⧸ N → M ⧸ N'`, for `d`-stable
submodules `N ≤ N'`. -/
noncomputable def quotientHomologyMapOfLE :
    d.quotientHomology hd N hN →ₗ[S] d.quotientHomology hd N' hN' :=
  homologyMap (N.mapQ N' LinearMap.id hNN') (d.mapQ_comp_mapQ_eq_zero hd N hN)
    (d.mapQ_comp_mapQ_eq_zero hd N' hN') (Submodule.linearMap_qext _ rfl)

/-- The map induced by `N ≤ N'` sends the class of `m` modulo `N` to its class modulo `N'`. -/
@[simp]
theorem quotientHomologyMapOfLE_mk (m : M) (hm : d m ∈ N) :
    quotientHomologyMapOfLE hd hN hN' hNN'
        (Submodule.Quotient.mk
          ⟨Submodule.Quotient.mk m, (Submodule.mk_mem_ker_mapQ_iff m).mpr hm⟩) =
      Submodule.Quotient.mk
        ⟨Submodule.Quotient.mk m, (Submodule.mk_mem_ker_mapQ_iff m).mpr (hNN' hm)⟩ :=
  homologyMap_mk _ _ _ _ _

/-- `quotientHomologyMapOfLE_mk` stated with `quotientHomologyClass`, for rewriting; `simp` unfolds
`quotientHomologyClass` and uses `quotientHomologyMapOfLE_mk` instead. -/
theorem quotientHomologyMapOfLE_quotientHomologyClass (m : M) (hm : d m ∈ N) :
    quotientHomologyMapOfLE hd hN hN' hNN' (quotientHomologyClass hd hN m hm) =
      quotientHomologyClass hd hN' m (hNN' hm) :=
  homologyMap_mk _ _ _ _ _

end OfLE

section Splitting

variable {d : M →ₗ[S] M} (hd : d ∘ₗ d = 0) {h v : M →ₗ[S] M} {N N' : Submodule S M}
  (hN : N ≤ N.comap d) (hN' : N' ≤ N'.comap d) (hNN' : N ≤ N') (hvN' : ∀ m, v m ∈ N')
  (hN'N : ∀ x ∈ N', ∃ u, x - v u ∈ N) (hh : ∀ m ∈ N, h m ∈ N) (hvd : ∀ m, d (v m) = v (d m))
  (hreg : ∀ m, v m ∈ N → m ∈ N) (hhom : ∀ m, d (h m) + h (d m) - v m ∈ N)

include hhom hh hNN' hvN' in
/-- If `d m ∈ N` then `d (h m) ∈ N'`: modulo `N`, `d (h m) = v m - h (d m)`. -/
private theorem d_h_mem {m : M} (hm : d m ∈ N) : d (h m) ∈ N' := by
  have : d (h m) = (d (h m) + h (d m) - v m) - h (d m) + v m := by abel
  rw [this]
  exact N'.add_mem (N'.sub_mem (hNN' (hhom m)) (hNN' (hh _ hm))) (hvN' m)

include hhom hh hNN' hvN' in
/-- If `b` is a boundary modulo `N`, then `h b` is a boundary modulo `N'`. -/
private theorem h_boundary {b w : M} (hbw : b - d w ∈ N) : h b - d (-h w) ∈ N' := by
  have : h b - d (-h w) = (d (h w) + h (d w) - v w) + v w + h (b - d w) := by
    simp only [map_neg, map_sub]
    abel
  rw [this]
  exact N'.add_mem (N'.add_mem (hNN' (hhom w)) (hvN' w)) (hNN' (hh _ hbw))

include hd hN hN'N hh hvd hreg hhom in
/-- If `a + h b` is a boundary modulo `N'` for cycles `a` and `b` modulo `N`, then `b` is a
boundary modulo `N`. -/
private theorem boundary_of_add_h {a b w : M} (ha : d a ∈ N) (hb : d b ∈ N)
    (habw : a + h b - d w ∈ N') : ∃ u, b - d u ∈ N := by
  obtain ⟨u, hu⟩ := hN'N _ habw
  refine ⟨u, hreg _ ?_⟩
  have hdd : d (d w) = 0 := congr($hd w)
  have : v (b - d u) = d (a + h b - d w - v u) - d a - (d (h b) + h (d b) - v b) + h (d b) +
      d (d w) := by
    simp only [map_sub, map_add, hvd]
    abel
  rw [this]
  exact N.add_mem (N.add_mem (N.sub_mem (N.sub_mem (hN hu) ha) (hhom b)) (hh _ hb))
    (hdd ▸ N.zero_mem)

include hd hN hN'N hh hvd hreg hhom in
/-- A cycle modulo `N` which is a boundary modulo `N'` is a boundary modulo `N`. -/
private theorem boundary_of_boundary {a w : M} (ha : d a ∈ N) (haw : a - d w ∈ N') :
    ∃ w', a - d w' ∈ N := by
  obtain ⟨u, hu⟩ := hN'N _ haw
  have hdd : d (d w) = 0 := congr($hd w)
  have hdu : d u ∈ N := hreg _ <| by
    have : v (d u) = d a - d (a - d w - v u) - d (d w) := by
      simp only [map_sub, hvd]
      abel
    rw [this, hdd, sub_zero]
    exact N.sub_mem ha (hN hu)
  refine ⟨w + h u, ?_⟩
  have : a - d (w + h u) = (a - d w - v u) - (d (h u) + h (d u) - v u) + h (d u) := by
    simp only [map_add]
    abel
  rw [this]
  exact N.add_mem (N.sub_mem hu (hhom u)) (hh _ hdu)

include hd hN hN'N hh hvd hreg hhom in
/-- A cycle `c` modulo `N'` is `(c - h u) + h u` for cycles `c - h u` and `u` modulo `N`. -/
private theorem exists_eq_add_h {c : M} (hc : d c ∈ N') :
    ∃ u, d u ∈ N ∧ d (c - h u) ∈ N := by
  obtain ⟨u, hu⟩ := hN'N _ hc
  have hdd : d (d c) = 0 := congr($hd c)
  have hdu : d u ∈ N := hreg _ <| by
    have : v (d u) = -d (d c - v u) := by
      simp only [map_sub, hvd, hdd]
      abel
    rw [this]
    exact N.neg_mem (hN hu)
  refine ⟨u, hdu, ?_⟩
  have : d (c - h u) = (d c - v u) - (d (h u) + h (d u) - v u) + h (d u) := by
    simp only [map_sub]
    abel
  rw [this]
  exact N.add_mem (N.sub_mem hu (hhom u)) (hh _ hdu)

include hvN' hhom hh in
/-- The map `H(M ⧸ N) → H(M ⧸ N')` induced by `h`. -/
private noncomputable def hHomology :
    d.quotientHomology hd N hN →ₗ[S] d.quotientHomology hd N' hN' :=
  Submodule.mapQ _ _ ((N.mapQ N' h fun m hm => hNN' (hh m hm)).restrict fun q hq => by
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
      rw [Submodule.mk_mem_ker_mapQ_iff] at hq
      rw [Submodule.mapQ_apply, Submodule.mk_mem_ker_mapQ_iff]
      exact d_h_mem hNN' hvN' hh hhom hq) fun ⟨q, hq⟩ hqb => by
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨w, hw⟩ := (Submodule.mk_mem_range_mapQ_iff m).mp hqb
    exact (Submodule.mk_mem_range_mapQ_iff (h m)).mpr ⟨-h w, h_boundary hNN' hvN' hh hhom hw⟩

private theorem hHomology_cls (m : M) (hm : d m ∈ N) :
    hHomology hd hN hN' hNN' hvN' hh hhom (quotientHomologyClass hd hN m hm) =
      quotientHomologyClass hd hN' (h m) (d_h_mem hNN' hvN' hh hhom hm) :=
  (rfl)

include hd hN hN'N hh hvd hreg hhom in
private theorem bijective_coprod_quotientHomologyMapOfLE_hHomology :
    Function.Bijective ((quotientHomologyMapOfLE hd hN hN' hNN').coprod
      (hHomology hd hN hN' hNN' hvN' hh hhom)) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun ⟨x, y⟩ hxy => ?_, fun z => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := exists_quotientHomologyClass_eq hd x
    obtain ⟨b, hb, rfl⟩ := exists_quotientHomologyClass_eq hd y
    rw [coprod_apply, quotientHomologyMapOfLE_quotientHomologyClass, hHomology_cls,
      quotientHomologyClass_add, quotientHomologyClass_eq_zero_iff] at hxy
    obtain ⟨w, hw⟩ := hxy
    obtain ⟨u, hu⟩ := boundary_of_add_h hd hN hN'N hh hvd hreg hhom ha hb hw
    have hy : quotientHomologyClass hd hN b hb = 0 :=
      (quotientHomologyClass_eq_zero_iff hd b hb).mpr ⟨u, hu⟩
    have hhb : h b - d (-h u) ∈ N' := h_boundary hNN' hvN' hh hhom hu
    have hx : quotientHomologyClass hd hN a ha = 0 := by
      rw [quotientHomologyClass_eq_zero_iff]
      refine boundary_of_boundary hd hN hN'N hh hvd hreg hhom ha (w := w + h u) ?_
      have : a - d (w + h u) = (a + h b - d w) - (h b - d (-h u)) := by
        simp only [map_add, map_neg]
        abel
      rw [this]
      exact N'.sub_mem hw hhb
    rw [hx, hy, Prod.mk_zero_zero]
  · obtain ⟨c, hc, rfl⟩ := exists_quotientHomologyClass_eq hd z
    obtain ⟨u, hu, hcu⟩ := exists_eq_add_h hd hN hN'N hh hvd hreg hhom hc
    refine ⟨(quotientHomologyClass hd hN (c - h u) hcu, quotientHomologyClass hd hN u hu), ?_⟩
    rw [coprod_apply, quotientHomologyMapOfLE_quotientHomologyClass, hHomology_cls,
      quotientHomologyClass_add]
    congr 1
    exact sub_add_cancel c (h u)

include hN'N hvd hreg in
/-- **Quotienting by a null-homotopic regular endomorphism doubles the homology.** Let `v` commute
with `d`, be regular modulo `N` (`v m ∈ N → m ∈ N`), and satisfy `d h + h d ≡ v` modulo `N` for an
endomorphism `h` with `h N ⊆ N`, and let `N' = N ⊔ range v`, given by `N ≤ N'`, `range v ≤ N'` and
`N' ≤ N ⊔ range v`. Then `H(M ⧸ N) × H(M ⧸ N) ≃ H(M ⧸ N')`, the class of `(a, b)` going to the
class of `a + h b`. -/
noncomputable def quotientHomologyProdEquiv :
    (d.quotientHomology hd N hN × d.quotientHomology hd N hN) ≃ₗ[S]
      d.quotientHomology hd N' hN' :=
  LinearEquiv.ofBijective _
    (bijective_coprod_quotientHomologyMapOfLE_hHomology hd hN hN' hNN' hvN' hN'N hh hvd hreg hhom)

include hN'N hvd hreg in
/-- The splitting sends the classes of cycles `a` and `b` modulo `N` to the class of `a + h b`
modulo `N'`. -/
@[simp]
theorem quotientHomologyProdEquiv_mk (a b : M) (ha : d a ∈ N) (hb : d b ∈ N) :
    quotientHomologyProdEquiv hd hN hN' hNN' hvN' hN'N hh hvd hreg hhom
        (Submodule.Quotient.mk
            ⟨Submodule.Quotient.mk a, (Submodule.mk_mem_ker_mapQ_iff a).mpr ha⟩,
          Submodule.Quotient.mk
            ⟨Submodule.Quotient.mk b, (Submodule.mk_mem_ker_mapQ_iff b).mpr hb⟩) =
      Submodule.Quotient.mk ⟨Submodule.Quotient.mk (a + h b),
        (Submodule.mk_mem_ker_mapQ_iff _).mpr (by
        rw [map_add]
        exact N'.add_mem (hNN' ha) (d_h_mem hNN' hvN' hh hhom hb))⟩ :=
  congr($(quotientHomologyMapOfLE_quotientHomologyClass hd hN hN' hNN' a ha) +
    $(hHomology_cls hd hN hN' hNN' hvN' hh hhom b hb))

end Splitting

end LinearMap
