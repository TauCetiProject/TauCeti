/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SquareZero.Quotient
public import TauCeti.Algebra.Module.GradedModule.Prod
public import TauCeti.Algebra.Module.GradedModule.Quotient
public import TauCeti.Algebra.Module.GradedModule.Shift

/-!
# The grading of the homology of a homogeneous endomorphism

Let `G` be an internal grading of a module `M` over a ring `R`,
indexed by an additive monoid with right cancellation.
Let `d` be a square-zero endomorphism of `M`, linear over a ring `S` acting compatibly with `R`,
which is homogeneous of some degree `r` for `G`. Then its homology `ker d ⧸ im d` inherits an
internal grading over `R`: the kernel of `d` carries the grading `TauCeti.InternalGrading.ker`,
and the image of `d` is homogeneous (`LinearMap.IsHomogeneous.isHomogeneous_range`), so
the grading descends to the quotient of the kernel by the image.

The ring `S` of `d` may be larger than the ring `R` of the grading. This is the situation of a
complex over a polynomial ring whose variables move the degree: the homogeneous pieces are then
submodules over the coefficients only, while `d` and its homology are modules over the whole
polynomial ring. An element of `S` which moves every homogeneous piece of `M` by a fixed degree
moves every homogeneous piece of the homology by the same degree
(`TauCeti.InternalGrading.smul_mem_homology_piece`).

The same applies to the homology `d.quotientHomology hd N hN` of the endomorphism induced on a
quotient `M ⧸ N` by a homogeneous `d`-stable submodule `N`
(`TauCeti.InternalGrading.quotientHomology`): its classes of degree `p` are the classes of the
elements `m` of degree `p` with `d m ∈ N`. Passing to a larger quotient `M ⧸ N'` along a
null-homotopic regular endomorphism splits the homology as two copies of the smaller one
(`LinearMap.quotientHomologyProdEquiv`). When the homotopy `h` is homogeneous of degree `s`, the
second copy is shifted by `s`: the splitting has degree zero from the product of the grading with
its shift by `-s` (`TauCeti.InternalGrading.isHomogeneous_quotientHomologyProdEquiv`), and the
degree-`p` piece of the larger quotient is the product of the degree-`p` and degree-`(p - s)`
pieces of the smaller one (`TauCeti.InternalGrading.quotientHomologyProdPieceEquiv`).

## Main definitions

* `TauCeti.InternalGrading.homology`: the grading of the homology of a homogeneous endomorphism.
* `TauCeti.InternalGrading.quotientHomology`: the grading of the homology of the endomorphism
  induced on a quotient by a homogeneous stable submodule.
* `TauCeti.InternalGrading.quotientHomologyProdPieceEquiv`: the splitting along a homogeneous
  homotopy of degree `s`, restricted to the pieces `H_p × H_(p - s) ≃ H'_p`.

## Main results

* `TauCeti.InternalGrading.mem_homology_piece_iff`: a homology class is homogeneous of degree `p`
  exactly when it is the class of a cycle of degree `p`, and
  `TauCeti.InternalGrading.homologyπ_mem_homology_piece`: the class of a homogeneous cycle is
  homogeneous of the same degree, so the quotient map from the cycles has degree zero
  (`TauCeti.InternalGrading.isHomogeneous_homologyπ`).
* `TauCeti.InternalGrading.smul_mem_homology_piece`: a scalar moving the degree of `M` by `q`
  moves the degree of the homology by `q`.
* `TauCeti.InternalGrading.mem_quotientHomology_piece_iff`: a class of quotient homology is
  homogeneous of degree `p` exactly when it is the class of an element of degree `p`.
* `TauCeti.InternalGrading.isHomogeneous_quotientHomologyProdEquiv`: the splitting along a
  homogeneous homotopy of degree `s` has degree zero from the product of the grading with its
  shift by `-s`.
-/

public section

open DirectSum

namespace TauCeti.InternalGrading

variable {ι : Type*} [DecidableEq ι] [AddRightCancelMonoid ι] {R S M : Type*}

section Semiring

variable [Semiring R] [Semiring S] [SMul R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) {r : ι}
  {d : M →ₗ[S] M} (hhom : LinearMap.IsHomogeneous d G.piece G.piece r)

include hhom in
/-- The intersection of the image and kernel of `d`, viewed inside the kernel, is homogeneous
for the grading of the kernel. No square-zero assumption is needed. -/
theorem isHomogeneous_boundariesInKer :
    SetLike.IsHomogeneous (G.ker hhom).piece d.boundariesInKer := by
  intro p z hz
  rw [LinearMap.mem_boundariesInKer, coe_decompose_ker]
  exact hhom.isHomogeneous_range p hz

end Semiring

section Ring

variable [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) {r : ι}
  {d : M →ₗ[S] M} (hhom : LinearMap.IsHomogeneous d G.piece G.piece r)
  (hd : d ∘ₗ d = 0)

/-- The internal grading of the homology `ker d ⧸ im d` of a homogeneous endomorphism: its
degree-`p` piece consists of the classes of the cycles of degree `p`. -/
noncomputable def homology : InternalGrading R (d.homology hd) ι :=
  (G.ker hhom).quotient d.boundariesInKer (G.isHomogeneous_boundariesInKer hhom)

/-- A homology class is homogeneous of degree `p` exactly when it is the class of a cycle of
degree `p`. -/
theorem mem_homology_piece_iff {p : ι} {y : d.homology hd} :
    y ∈ (G.homology hhom hd).piece p ↔
      ∃ z : _root_.LinearMap.ker d, (z : M) ∈ G.piece p ∧ d.homologyπ hd z = y := by
  simp only [homology, mem_quotient_piece_iff, mem_ker_piece, LinearMap.homologyπ_apply]

/-- The class of a cycle of degree `p` is a homology class of degree `p`. -/
theorem homologyπ_mem_homology_piece {p : ι} {z : _root_.LinearMap.ker d}
    (hz : (z : M) ∈ G.piece p) : d.homologyπ hd z ∈ (G.homology hhom hd).piece p :=
  (G.mem_homology_piece_iff hhom hd).mpr ⟨z, hz, rfl⟩

/-- The quotient map from the cycles onto the homology has degree zero. -/
theorem isHomogeneous_homologyπ :
    LinearMap.IsHomogeneous (d.homologyπ hd) (G.ker hhom).piece (G.homology hhom hd).piece 0 :=
  LinearMap.isHomogeneous_def.2 fun _ z hz ↦ by
    rw [add_zero]
    exact G.homologyπ_mem_homology_piece hhom hd ((G.mem_ker_piece hhom).1 hz)

/-- An element of the ring of `d` which moves every homogeneous piece of `M` up by `q` moves every
homogeneous piece of the homology of `d` up by `q`. -/
theorem smul_mem_homology_piece {s : S} {q : ι}
    (hs : ∀ ⦃p : ι⦄ ⦃x : M⦄, x ∈ G.piece p → s • x ∈ G.piece (p + q)) {p : ι}
    {y : d.homology hd} (hy : y ∈ (G.homology hhom hd).piece p) :
    s • y ∈ (G.homology hhom hd).piece (p + q) := by
  obtain ⟨z, hz, rfl⟩ := (G.mem_homology_piece_iff hhom hd).mp hy
  rw [← map_smul]
  exact G.homologyπ_mem_homology_piece hhom hd (z := s • z) (hs hz)

end Ring

section QuotientHomology

variable [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) {r : ι}
  {d : M →ₗ[S] M} (hdG : LinearMap.IsHomogeneous d G.piece G.piece r)
  (hd : d ∘ₗ d = 0) {N : Submodule S M} (hN : N ≤ N.comap d)
  (hNG : SetLike.IsHomogeneous G.piece N)

/-- The internal grading of the homology of the endomorphism induced by `d` on `M ⧸ N`, for a
homogeneous `d` and a homogeneous `d`-stable submodule `N`: its degree-`p` piece consists of the
classes of the elements of degree `p` whose image under `d` lies in `N`. -/
noncomputable def quotientHomology : InternalGrading R (d.quotientHomology hd N hN) ι :=
  (G.quotient N hNG).homology (G.isHomogeneous_mapQ N hNG hdG hN) (d.mapQ_comp_mapQ_eq_zero hd N hN)

/-- A class of quotient homology is homogeneous of degree `p` exactly when it is the class of an
element `m` of degree `p` with `d m ∈ N`. -/
theorem mem_quotientHomology_piece_iff {p : ι} {y : d.quotientHomology hd N hN} :
    y ∈ (G.quotientHomology hdG hd hN hNG).piece p ↔
      ∃ m ∈ G.piece p, ∃ hm : d m ∈ N, LinearMap.quotientHomologyClass hd hN m hm = y := by
  rw [quotientHomology, mem_homology_piece_iff]
  constructor
  · rintro ⟨⟨q, hq⟩, hqp, rfl⟩
    obtain ⟨m, hm, rfl⟩ := (G.mem_quotient_piece_iff N hNG).1 hqp
    exact ⟨m, hm, (Submodule.mk_mem_ker_mapQ_iff m).1 hq, by
      rw [LinearMap.quotientHomologyClass_def, LinearMap.homologyπ_apply]⟩
  · rintro ⟨m, hm, hdm, rfl⟩
    exact ⟨⟨_, (Submodule.mk_mem_ker_mapQ_iff m).2 hdm⟩, G.mk_mem_quotient_piece N hNG hm, by
      rw [LinearMap.quotientHomologyClass_def, LinearMap.homologyπ_apply]⟩

/-- The class of an element of degree `p` is a class of quotient homology of degree `p`. -/
theorem quotientHomologyClass_mem_quotientHomology_piece {p : ι} {m : M} (hmp : m ∈ G.piece p)
    (hm : d m ∈ N) :
    LinearMap.quotientHomologyClass hd hN m hm ∈ (G.quotientHomology hdG hd hN hNG).piece p :=
  (G.mem_quotientHomology_piece_iff hdG hd hN hNG).2 ⟨m, hmp, hm, rfl⟩

/-- A linear map out of quotient homology is homogeneous of degree `q` as soon as it sends the
class of every element `m` of degree `p` with `d m ∈ N` into the degree-`(p + q)` piece. -/
theorem isHomogeneous_of_quotientHomologyClass {P σ : Type*} [AddCommMonoid P] [Module R P]
    [SetLike σ P] {ℬ : ι → σ} {q : ι} {f : d.quotientHomology hd N hN →ₗ[R] P}
    (hf : ∀ (p : ι) (m : M), m ∈ G.piece p → ∀ hm : d m ∈ N,
      f (LinearMap.quotientHomologyClass hd hN m hm) ∈ ℬ (p + q)) :
    LinearMap.IsHomogeneous f (G.quotientHomology hdG hd hN hNG).piece ℬ q :=
  LinearMap.isHomogeneous_def.2 fun p _ hy ↦ by
    obtain ⟨m, hmp, hm, rfl⟩ := (G.mem_quotientHomology_piece_iff hdG hd hN hNG).1 hy
    exact hf p m hmp hm

end QuotientHomology

end TauCeti.InternalGrading

namespace TauCeti.InternalGrading

section Splitting

variable {ι : Type*} [DecidableEq ι] [AddCommGroup ι] {R S M : Type*}
  [Ring R] [Ring S] [SMul R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  (G : InternalGrading R M ι) {r : ι}
  {d : M →ₗ[S] M} (hdG : LinearMap.IsHomogeneous d G.piece G.piece r)
  (hd : d ∘ₗ d = 0) {N : Submodule S M} (hN : N ≤ N.comap d)
  (hNG : SetLike.IsHomogeneous G.piece N) {h v : M →ₗ[S] M} {N' : Submodule S M}
  (hN' : N' ≤ N'.comap d)
  (hN'G : SetLike.IsHomogeneous G.piece N') (hNN' : N ≤ N') (hvN' : ∀ m, v m ∈ N')
  (hN'N : ∀ x ∈ N', ∃ u, x - v u ∈ N) (hh : ∀ m ∈ N, h m ∈ N)
  (hreg : ∀ m, v m ∈ N → m ∈ N) (hhom : ∀ m, d (h m) + h (d m) - v m ∈ N) {s : ι}
  (hhG : LinearMap.IsHomogeneous h G.piece G.piece s)

include hhG in
/-- **The splitting along a homogeneous homotopy is homogeneous.** If the homotopy `h` in
`LinearMap.quotientHomologyProdEquiv` is homogeneous of degree `s`, then the splitting
`H(M ⧸ N) × H(M ⧸ N) ≃ H(M ⧸ N')`, `(a, b) ↦ a + h b`, has degree zero when its second factor is
graded by the shift by `-s`. -/
theorem isHomogeneous_quotientHomologyProdEquiv :
    LinearMap.IsHomogeneous
      ((LinearMap.quotientHomologyProdEquiv hd hN hN' hNN' hvN' hN'N hh hreg
        hhom).restrictScalars R).toLinearMap
      ((G.quotientHomology hdG hd hN hNG).prod
        ((G.quotientHomology hdG hd hN hNG).shift (-s))).piece
      (G.quotientHomology hdG hd hN' hN'G).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  rintro p ⟨x, y⟩ hxy
  rw [prod_piece, Submodule.mem_prod, shift_piece] at hxy
  obtain ⟨a, hap, ha, rfl⟩ := (G.mem_quotientHomology_piece_iff hdG hd hN hNG).1 hxy.1
  obtain ⟨b, hbp, hb, rfl⟩ := (G.mem_quotientHomology_piece_iff hdG hd hN hNG).1 hxy.2
  have hhb : h b ∈ G.piece p := by
    simpa only [neg_add_cancel_right] using hhG.map_mem hbp
  rw [add_zero, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
    LinearMap.quotientHomologyClass_def, LinearMap.quotientHomologyClass_def,
    LinearMap.quotientHomologyProdEquiv_mk hd hN hN' hNN' hvN' hN'N hh hreg hhom a b ha hb]
  have hab : d (a + h b) ∈ N' := by
    rw [map_add]
    exact N'.add_mem (hNN' ha) (LinearMap.map_map_mem_of_homotopy hNN' hvN' hh hhom hb)
  simpa only [LinearMap.quotientHomologyClass_def] using
    G.quotientHomologyClass_mem_quotientHomology_piece hdG hd hN' hN'G (add_mem hap hhb) hab

include hhG in
/-- **Graded doubling of quotient homology.** If the homotopy `h` in
`LinearMap.quotientHomologyProdEquiv` is homogeneous of degree `s`, its splitting restricts to an
equivalence from the product of the degree-`p` and degree-`(p - s)` pieces of `H(M ⧸ N)` onto the
degree-`p` piece of `H(M ⧸ N')`. -/
noncomputable def quotientHomologyProdPieceEquiv (p : ι) :
    ((G.quotientHomology hdG hd hN hNG).piece p ×
        (G.quotientHomology hdG hd hN hNG).piece (p - s)) ≃ₗ[R]
      (G.quotientHomology hdG hd hN' hN'G).piece p :=
  (Submodule.prodEquiv _ _).symm ≪≫ₗ
    LinearEquiv.ofEq _ _ (by rw [prod_piece, shift_piece, sub_eq_add_neg]) ≪≫ₗ
    (G.isHomogeneous_quotientHomologyProdEquiv hdG hd hN hNG hN' hN'G hNN' hvN' hN'N hh hreg
      hhom hhG).pieceEquiv p

/-- The graded splitting is the splitting `LinearMap.quotientHomologyProdEquiv` on underlying
classes. -/
@[simp]
theorem coe_quotientHomologyProdPieceEquiv_apply (p : ι)
    (x : (G.quotientHomology hdG hd hN hNG).piece p ×
      (G.quotientHomology hdG hd hN hNG).piece (p - s)) :
    (G.quotientHomologyProdPieceEquiv hdG hd hN hNG hN' hN'G hNN' hvN' hN'N hh hreg hhom hhG
        p x : d.quotientHomology hd N' hN') =
      LinearMap.quotientHomologyProdEquiv hd hN hN' hNN' hvN' hN'N hh hreg hhom
        ((x.1 : d.quotientHomology hd N hN), (x.2 : d.quotientHomology hd N hN)) := by
  simp [quotientHomologyProdPieceEquiv]

end Splitting

end TauCeti.InternalGrading
