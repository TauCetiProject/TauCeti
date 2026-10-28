/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.PtSimplex
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
public import TauCeti.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-!
# Homotopy groups of simplicial modules

Let `G` be a simplicial module over a ring `R`, for instance a simplicial abelian group regarded as
a simplicial `ℤ`-module. Its underlying simplicial set `G ⋙ forget (ModuleCat R)` is a Kan complex
(`CategoryTheory.SimplicialObject.kanComplex_comp_forget_moduleCat`), so it has combinatorial
homotopy groups `SSet.KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) 0` at the vertex `0`, and a
pointed set of path components `SSet.KanComplex.π 0 (G ⋙ forget (ModuleCat R)) 0`. This file
identifies them with the homology of the normalized Moore complex `N(G)`, naturally in `G`:

`π_{n+1}(G, 0) ≃+ H_{n+1}(N(G))`, `π₀(G, 0) ≃ H₀(N(G))`

(`CategoryTheory.SimplicialObject.piAddEquivNormalizedMooreComplexHomology`,
`CategoryTheory.SimplicialObject.piZeroEquivNormalizedMooreComplexHomology`), and likewise with the
homology of the alternating face map complex `C(G)`, the unnormalized complex
(`CategoryTheory.SimplicialObject.piAddEquivAlternatingFaceMapComplexHomology`,
`CategoryTheory.SimplicialObject.piZeroEquivAlternatingFaceMapComplexHomology`).

The identification is elementary. A pointed `(n + 1)`-simplex of `G` at `0` is an element
`g ∈ G_{n+1}` all of whose faces vanish (`CategoryTheory.SimplicialObject.ptSimplexEquiv`), that
is, a cycle of `N(G)` of degree `n + 1`. If two such simplices `p` and `q` are the faces `0` and `1`
of an `(n + 2)`-simplex `y` whose other faces vanish, then `p - q` is the boundary of `y`; so
homotopic pointed simplices have the same homology class. The product of the classes of `p` and
`q` is witnessed by the simplex `s_{n+1} p + s_n q`, so it is the class of the sum `p + q`
(`CategoryTheory.SimplicialObject.mk_mul_mk_eq_mk_add`).

The comparison is made with `C(G)`, whose terms are the modules `G_n` themselves, through
Mathlib's Dold–Kan projector `AlgebraicTopology.DoldKan.PInfty`: a chain endomorphism of `C(G)`
homotopic to the identity, whose values have vanishing faces `δᵢ` for `i ≥ 1`, and which fixes
such elements. So every homology class of `C(G)` is represented by a pointed simplex, and a
pointed simplex `g` that is a boundary `d y` in `C(G)` is the face `δ₀` of `PInfty y`, whose other
faces vanish, so it is homotopic to the constant simplex. The passage to `N(G)` is then the
homotopy equivalence
`AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex`. In degree
zero a homotopy of vertices restricts to an edge, whose boundary is their difference, and
conversely an edge `e` with `d e = p - q` is corrected to the edge `e + s₀ (q - δ₁ e)` from `q`
to `p`.

## Main declarations

* `CategoryTheory.SimplicialObject.ptSimplexEquiv`: pointed `(n + 1)`-simplices of `G` at `0` are
  the elements of `G_{n+1}` all of whose faces vanish.
* `CategoryTheory.SimplicialObject.mk_mul_mk_eq_mk_add`: the product of the classes of two pointed
  simplices is the class of their sum.
* `CategoryTheory.SimplicialObject.piAddEquivAlternatingFaceMapComplexHomology`: the isomorphism
  `π_{n+1}(G, 0) ≃+ H_{n+1}(C(G))`, with its value on a class
  (`CategoryTheory.SimplicialObject.piAddEquivAlternatingFaceMapComplexHomology_mk`) and its
  naturality (`CategoryTheory.SimplicialObject.piAddEquivAlternatingFaceMapComplexHomology_map`).
* `CategoryTheory.SimplicialObject.piAddEquivNormalizedMooreComplexHomology`: the isomorphism
  `π_{n+1}(G, 0) ≃+ H_{n+1}(N(G))` and its naturality
  (`CategoryTheory.SimplicialObject.piAddEquivNormalizedMooreComplexHomology_map`).
* `CategoryTheory.SimplicialObject.piZeroEquivAlternatingFaceMapComplexHomology`,
  `CategoryTheory.SimplicialObject.piZeroEquivNormalizedMooreComplexHomology`: the bijections in
  degree zero, with their naturality.

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967, §17,
  for the homotopy groups of simplicial groups and the normalized complex.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Chapter III, §2, for simplicial abelian groups.
-/

public noncomputable section

universe u

open CategoryTheory Simplicial Opposite AlgebraicTopology AlgebraicTopology.DoldKan SSet DoldKan

namespace CategoryTheory.SimplicialObject

variable {R : Type*} [Ring R] (G : SimplicialObject (ModuleCat.{u} R)) {n : ℕ}

/-! ### Elementwise facts about the alternating face map complex -/

/-- The differential of the alternating face map complex of a simplicial module, on an element. -/
private lemma d_apply (z : G _⦋n + 1⦌) :
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).d (n + 1) n z =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • G.δ i z := by
  simp

/-- On an element whose faces `δᵢ`, `i ≥ 1`, vanish, the differential of the alternating face map
complex is the face `δ₀`. -/
private lemma d_apply_of_δ_succ_eq_zero {z : G _⦋n + 1⦌}
    (hz : ∀ i : Fin (n + 1), G.δ i.succ z = 0) :
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).d (n + 1) n z = G.δ 0 z := by
  rw [d_apply]
  simp [Fin.sum_univ_succ, hz]

/-- The faces `δᵢ`, `i ≥ 1`, vanish on the values of the projector `PInfty`. -/
private lemma δ_succ_PInfty_f_apply (z : G _⦋n + 1⦌) (i : Fin (n + 1)) :
    G.δ i.succ ((PInfty.f (n + 1) : G _⦋n + 1⦌ ⟶ G _⦋n + 1⦌) z) = 0 := by
  have := (HigherFacesVanish.of_P (X := G) (n + 1) n) i (by omega)
  rw [← PInfty_f] at this
  exact congr($this z)

/-- The projector `PInfty` fixes the elements whose faces `δᵢ`, `i ≥ 1`, vanish. -/
private lemma PInfty_f_apply_of_δ_succ_eq_zero {z : G _⦋n + 1⦌}
    (hz : ∀ i : Fin (n + 1), G.δ i.succ z = 0) :
    (PInfty.f (n + 1) : G _⦋n + 1⦌ ⟶ G _⦋n + 1⦌) z = z := by
  let N : Submodule R (G _⦋n + 1⦌) := ⨅ i : Fin (n + 1), LinearMap.ker (G.δ i.succ).hom
  have hv : HigherFacesVanish (n + 1) (ModuleCat.ofHom N.subtype ≫ 𝟙 (G _⦋n + 1⦌)) :=
    fun i _ ↦ by ext ⟨z, hz⟩; exact (Submodule.mem_iInf _).1 hz i
  have := hv.comp_P_eq_self
  rw [Category.comp_id, ← PInfty_f] at this
  exact congr($this ⟨z, (Submodule.mem_iInf _).2 hz⟩)

/-- The projector `PInfty` commutes with the differential of the alternating face map complex, on
elements. -/
private lemma PInfty_f_d_apply (z : G _⦋n + 2⦌) :
    (PInfty.f (n + 1) : G _⦋n + 1⦌ ⟶ G _⦋n + 1⦌)
        (((alternatingFaceMapComplex (ModuleCat R)).obj G).d (n + 2) (n + 1) z) =
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).d (n + 2) (n + 1)
        ((PInfty.f (n + 2) : G _⦋n + 2⦌ ⟶ G _⦋n + 2⦌) z) :=
  (HomologicalComplex.Hom.comm_apply PInfty (n + 2) (n + 1) z).symm

/-! ### Pointed simplices of a simplicial module -/

/-- The constant `m`-simplex at `0` of the underlying simplicial set of a simplicial module is
`0`. -/
private lemma yonedaEquiv_const_zero (m : ℕ) :
    SSet.yonedaEquiv (SSet.const (0 : G _⦋0⦌) : Δ[m] ⟶ G ⋙ forget (ModuleCat R)) = 0 :=
  map_zero (G.map _).hom

/-- An `(m + 1)`-simplex of `G` whose face `δⱼ` is the simplex of a morphism `f` is a morphism whose
face `j` is `f`. -/
private lemma δ_comp_yonedaEquiv_symm_eq {m : ℕ} {w : G _⦋m + 1⦌} {j : Fin (m + 2)}
    {f : Δ[m] ⟶ G ⋙ forget (ModuleCat R)} (h : G.δ j w = SSet.yonedaEquiv f) :
    stdSimplex.δ j ≫ (SSet.yonedaEquiv.symm w : Δ[m + 1] ⟶ G ⋙ forget (ModuleCat R)) = f := by
  rw [stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_eq]
  exact h

/-- An `(m + 1)`-simplex of `G` whose face `δⱼ` vanishes is a morphism whose face `j` is constant
at `0`. -/
private lemma δ_comp_yonedaEquiv_symm_eq_const {m : ℕ} {w : G _⦋m + 1⦌} {j : Fin (m + 2)}
    (h : G.δ j w = 0) :
    stdSimplex.δ j ≫ (SSet.yonedaEquiv.symm w : Δ[m + 1] ⟶ G ⋙ forget (ModuleCat R)) =
      SSet.const (0 : G _⦋0⦌) :=
  δ_comp_yonedaEquiv_symm_eq G (h.trans (yonedaEquiv_const_zero G m).symm)

/-- The face `δⱼ` of the simplex of a morphism `f : Δ[m + 1] ⟶ G` is the simplex of the face `j`
of `f`. -/
private lemma δ_yonedaEquiv {m : ℕ} (f : Δ[m + 1] ⟶ G ⋙ forget (ModuleCat R)) (j : Fin (m + 2)) :
    G.δ j (SSet.yonedaEquiv f) = (SSet.yonedaEquiv (stdSimplex.δ j ≫ f) : G _⦋m⦌) :=
  (stdSimplex.yonedaEquiv_δ_comp f j).symm

/-- The pointed `(n + 1)`-simplices of the underlying simplicial set of a simplicial module `G` at
the vertex `0` are the elements of `G_{n+1}` all of whose faces vanish, that is, the cycles of
degree `n + 1` of the normalized Moore complex. -/
def ptSimplexEquiv :
    SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌) ≃
      ↥(⨅ i : Fin (n + 2), LinearMap.ker (G.δ i).hom) where
  toFun p := ⟨SSet.yonedaEquiv p.map, (Submodule.mem_iInf _).2 fun i ↦ by
    rw [LinearMap.mem_ker]
    exact (δ_yonedaEquiv G p.map i).trans ((congrArg SSet.yonedaEquiv (p.δ_map i)).trans
      (yonedaEquiv_const_zero G n))⟩
  invFun g :=
    { map := (SSet.yonedaEquiv.symm g.1 : Δ[n + 1] ⟶ G ⋙ forget (ModuleCat R))
      comm := by
        ext i : 1
        simp only [boundary.ι_ι_assoc]
        exact δ_comp_yonedaEquiv_symm_eq_const G ((Submodule.mem_iInf _).1 g.2 i) }
  left_inv p := by ext : 1; simp
  right_inv g := by ext : 1; simp

variable {G}

@[simp]
lemma coe_ptSimplexEquiv_apply
    (p : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)) :
    (ptSimplexEquiv G p : G _⦋n + 1⦌) = SSet.yonedaEquiv p.map :=
  (rfl)

@[simp]
lemma ptSimplexEquiv_symm_apply_map (g : ↥(⨅ i : Fin (n + 2), LinearMap.ker (G.δ i).hom)) :
    ((ptSimplexEquiv G).symm g).map =
      (SSet.yonedaEquiv.symm g.1 : Δ[n + 1] ⟶ G ⋙ forget (ModuleCat R)) :=
  (rfl)

/-- The faces of an element of `G_{n+1}` corresponding to a pointed simplex vanish. -/
private lemma δ_ptSimplexEquiv
    (p : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)) (i : Fin (n + 2)) :
    G.δ i (ptSimplexEquiv G p) = 0 :=
  (Submodule.mem_iInf _).1 (ptSimplexEquiv G p).2 i

/-- In the homotopy group of a simplicial module, the product of the classes of two pointed
simplices is the class of their sum. -/
lemma mk_mul_mk_eq_mk_add
    (p q : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)) :
    KanComplex.π.mk p * KanComplex.π.mk q =
      KanComplex.π.mk ((ptSimplexEquiv G).symm (ptSimplexEquiv G p + ptSimplexEquiv G q)) := by
  -- The product is witnessed by the `(n + 2)`-simplex `s_{n+1} p + s_n q`.
  set x : G _⦋n + 1⦌ := (ptSimplexEquiv G p).1
  set y : G _⦋n + 1⦌ := (ptSimplexEquiv G q).1
  have hx (i : Fin (n + 2)) : G.δ i x = 0 := δ_ptSimplexEquiv p i
  have hy (i : Fin (n + 2)) : G.δ i y = 0 := δ_ptSimplexEquiv q i
  set w : G _⦋n + 2⦌ := G.σ (Fin.last (n + 1)) x + G.σ (Fin.last n).castSucc y
  have h₂ : G.δ (Fin.last n).succ.succ w = x := by
    have h₁ := congr($(G.δ_comp_σ_succ (i := Fin.last (n + 1))) x)
    have h₂ := congr($(G.δ_comp_σ_of_gt (i := Fin.last (n + 1)) (j := Fin.last n)
      (Fin.castSucc_lt_last _)) y)
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply, hy, map_zero, Fin.succ_last] at h₁ h₂
    simp [w, h₁, h₂]
  have h₁ : G.δ (Fin.last n).castSucc.succ w = x + y := by
    have h₁ := congr($(G.δ_comp_σ_self (i := Fin.last (n + 1))) x)
    have h₂ := congr($(G.δ_comp_σ_succ (i := (Fin.last n).castSucc)) y)
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at h₁ h₂
    rw [show (Fin.last (n + 1)).castSucc = (Fin.last n).castSucc.succ from Fin.ext (by simp)] at h₁
    simp [w, h₁, h₂]
  have h₀ : G.δ (Fin.last n).castSucc.castSucc w = y := by
    have h₁ := congr($(G.δ_comp_σ_of_le (i := (Fin.last n).castSucc) (j := Fin.last n)
      le_rfl) x)
    have h₂ := congr($(G.δ_comp_σ_self (i := (Fin.last n).castSucc)) y)
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply, hx, map_zero, Fin.succ_last] at h₁ h₂
    simp [w, h₁, h₂]
  have hlt (j : Fin (n + 3)) (hj : j < (Fin.last n).castSucc.castSucc) : G.δ j w = 0 := by
    obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
    rw [Fin.lt_def] at hj
    simp only [Fin.val_castSucc, Fin.val_last] at hj
    have h₁ := congr($(G.δ_comp_σ_of_le (i := i) (j := Fin.last n)
      (Fin.le_def.2 (by simp; omega))) x)
    obtain _ | m := n
    · omega
    have h₂ := congr($(G.δ_comp_σ_of_le (i := i) (j := (Fin.last m).castSucc)
      (Fin.le_def.2 (by simp; omega))) y)
    rw [show (Fin.last m).castSucc.succ = (Fin.last (m + 1)).castSucc from Fin.ext (by simp)]
      at h₂
    simp only [ModuleCat.comp_apply, hx, hy, map_zero, Fin.succ_last] at h₁ h₂
    simp [w, h₁, h₂]
  refine KanComplex.π.mul_mk_eq_iff.2 ⟨{
    map := (SSet.yonedaEquiv.symm w : Δ[n + 2] ⟶ G ⋙ forget (ModuleCat R))
    δ_castSucc_castSucc_map := δ_comp_yonedaEquiv_symm_eq G h₀
    δ_succ_castSucc_map := δ_comp_yonedaEquiv_symm_eq G (h₁.trans (by simp [x, y]))
    δ_succ_succ_map := δ_comp_yonedaEquiv_symm_eq G h₂
    δ_map_of_lt := fun j hj ↦ δ_comp_yonedaEquiv_symm_eq_const G (hlt j hj)
    δ_map_of_gt := fun j hj ↦ absurd hj (not_lt.2 (Fin.le_last j)) }⟩

/-- The constant pointed simplex corresponds to `0`. -/
private lemma ptSimplexEquiv_const :
    ptSimplexEquiv G (.const : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)) =
      0 :=
  Subtype.ext (yonedaEquiv_const_zero G (n + 1))

/-! ### The comparison with the homology of the alternating face map complex -/

variable (G n) in
/-- The homology class in the alternating face map complex of an element of `G_{n+1}` all of
whose faces vanish. -/
private def mooreCyclesHomologyClass :
    ↥(⨅ i : Fin (n + 2), LinearMap.ker (G.δ i).hom) →ₗ[R]
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology (n + 1) :=
  ((alternatingFaceMapComplex (ModuleCat R)).obj G).moduleCatHomologyClass (m := n) (by simp)
    (Submodule.subtype _) fun z ↦ by
    rw [d_apply]
    exact Finset.sum_eq_zero fun i _ ↦ by
      simp [LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 z.2 i)]

/-- Two pointed simplices related by `SSet.PtSimplex.RelStruct₀` have the same homology class:
if `y` has faces `p`, `q`, `0`, …, `0`, then `p - q` is the boundary of `y`. -/
private lemma mooreCyclesHomologyClass_eq_of_relStruct₀
    {p q : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)}
    (h : p.RelStruct₀ q) :
    mooreCyclesHomologyClass G n (ptSimplexEquiv G p) =
      mooreCyclesHomologyClass G n (ptSimplexEquiv G q) := by
  rw [← sub_eq_zero, ← map_sub, mooreCyclesHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_eq_zero_iff (p := n + 2) _ _ _ _ (by simp)]
  refine ⟨SSet.yonedaEquiv h.map, ?_⟩
  have h₀ : G.δ 0 (SSet.yonedaEquiv h.map) = SSet.yonedaEquiv p.map := by
    rw [δ_yonedaEquiv]
    exact congrArg _ h.δ_castSucc_map
  have h₁ : G.δ 1 (SSet.yonedaEquiv h.map) = SSet.yonedaEquiv q.map := by
    rw [δ_yonedaEquiv]
    exact congrArg _ h.δ_succ_map
  have h₂ (j : Fin (n + 1)) : G.δ j.succ.succ (SSet.yonedaEquiv h.map) = 0 := by
    rw [δ_yonedaEquiv, h.δ_map_of_gt j.succ.succ (by simp [Fin.lt_def]), yonedaEquiv_const_zero]
  rw [d_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [h₀, h₁, h₂, sub_eq_add_neg]

/-- The homology class in the alternating face map complex of a pointed simplex, on homotopy
classes. -/
private def piToHomology :
    Additive (KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) →+
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology (n + 1) :=
  AddMonoidHom.mk' (fun a ↦ KanComplex.π.lift
    (fun p ↦ mooreCyclesHomologyClass G n (ptSimplexEquiv G p))
    (fun _ _ h ↦ mooreCyclesHomologyClass_eq_of_relStruct₀ h.relStruct₀) a.toMul) fun a b ↦ by
    induction a using Additive.rec with | ofMul a
    induction b using Additive.rec with | ofMul b
    induction a with | mk p
    induction b with | mk q
    rw [← ofMul_mul, toMul_ofMul, toMul_ofMul, toMul_ofMul, mk_mul_mk_eq_mk_add,
      KanComplex.π.lift_mk, KanComplex.π.lift_mk, KanComplex.π.lift_mk, Equiv.apply_symm_apply,
      map_add]

private lemma piToHomology_mk
    (p : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)) :
    piToHomology (.ofMul (KanComplex.π.mk p)) =
      mooreCyclesHomologyClass G n (ptSimplexEquiv G p) :=
  KanComplex.π.lift_mk _ _ p

/-- A pointed simplex whose homology class in the alternating face map complex vanishes is
homotopic to the constant simplex: if it is the boundary of `y`, it is the boundary, and so the
face `δ₀`, of `PInfty y`, whose other faces vanish. -/
private lemma mk_eq_mk_const_of_mooreCyclesHomologyClass_eq_zero
    {p : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌)}
    (hp : mooreCyclesHomologyClass G n (ptSimplexEquiv G p) = 0) :
    KanComplex.π.mk p = KanComplex.π.mk .const := by
  rw [mooreCyclesHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_eq_zero_iff (p := n + 2) _ _ _ _ (by simp)] at hp
  obtain ⟨y, hy⟩ := hp
  have hz :
      G.δ 0 ((PInfty.f (n + 2) : G _⦋n + 2⦌ ⟶ G _⦋n + 2⦌) y) = SSet.yonedaEquiv p.map := by
    rw [← d_apply_of_δ_succ_eq_zero G (δ_succ_PInfty_f_apply G y), ← PInfty_f_d_apply, hy]
    exact PInfty_f_apply_of_δ_succ_eq_zero G fun i ↦ δ_ptSimplexEquiv p i.succ
  have hz' (j : Fin (n + 2)) := δ_succ_PInfty_f_apply G y j
  exact KanComplex.π.mk_eq_mk_iff.2
    ⟨{ map := (SSet.yonedaEquiv.symm ((PInfty.f (n + 2) : G _⦋n + 2⦌ ⟶ G _⦋n + 2⦌) y) :
         Δ[n + 2] ⟶ G ⋙ forget (ModuleCat R))
       δ_castSucc_map := δ_comp_yonedaEquiv_symm_eq G hz
       δ_succ_map := δ_comp_yonedaEquiv_symm_eq_const G (hz' 0)
       δ_map_of_lt := fun j hj ↦ absurd hj (Fin.not_lt_zero _)
       δ_map_of_gt := fun j hj ↦ by
         obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero ((Fin.succ_pos 0).trans hj).ne'
         exact δ_comp_yonedaEquiv_symm_eq_const G (hz' j) }⟩

/-- Two pointed simplices with the same homology class are homotopic: their difference is
homotopic to the constant simplex. -/
private lemma piToHomology_injective : Function.Injective (piToHomology (G := G) (n := n)) := by
  intro a b hab
  induction a using Additive.rec with | ofMul a
  induction b using Additive.rec with | ofMul b
  induction a with | mk p
  induction b with | mk q
  rw [piToHomology_mk, piToHomology_mk] at hab
  set r := (ptSimplexEquiv G).symm (ptSimplexEquiv G p - ptSimplexEquiv G q)
  have hr : KanComplex.π.mk r = KanComplex.π.mk .const :=
    mk_eq_mk_const_of_mooreCyclesHomologyClass_eq_zero <| by
      rw [Equiv.apply_symm_apply, map_sub, hab, sub_self]
  have hp : KanComplex.π.mk p = KanComplex.π.mk q * KanComplex.π.mk r := by
    rw [mk_mul_mk_eq_mk_add, Equiv.apply_symm_apply, add_sub_cancel, Equiv.symm_apply_apply]
  rw [hp, hr, mk_mul_mk_eq_mk_add, ptSimplexEquiv_const, add_zero, Equiv.symm_apply_apply]

/-- Every homology class of the alternating face map complex is the class of a pointed simplex:
the class of a cycle `x` is the class of `PInfty x`, whose faces vanish. -/
private lemma piToHomology_surjective : Function.Surjective (piToHomology (G := G) (n := n)) := by
  intro c
  obtain ⟨x, hx, rfl⟩ :=
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).exists_homologyπ_moduleCatCyclesMk_eq n
      (by simp) c
  -- `PInfty` and its homotopy are stated for `K[G]`, which is by definition the alternating face
  -- map complex `(alternatingFaceMapComplex _).obj G`
  have hx₀ : K[G].d (n + 1) n x = 0 := hx
  have hx' : (PInfty.f (n + 1) : G _⦋n + 1⦌ ⟶ G _⦋n + 1⦌) x ∈
      ⨅ i : Fin (n + 2), LinearMap.ker (G.δ i).hom := by
    refine (Submodule.mem_iInf _).2 fun i ↦ LinearMap.mem_ker.2 ?_
    cases i using Fin.cases with
    | zero =>
      rw [← d_apply_of_δ_succ_eq_zero G (δ_succ_PInfty_f_apply G x),
        HomologicalComplex.Hom.comm_apply, hx₀, map_zero]
    | succ i => exact δ_succ_PInfty_f_apply G x i
  refine ⟨.ofMul (KanComplex.π.mk ((ptSimplexEquiv G).symm ⟨_, hx'⟩)), ?_⟩
  rw [piToHomology_mk, Equiv.apply_symm_apply, mooreCyclesHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_apply]
  -- `x' - x` is the boundary of `h x` for the homotopy `h` from `PInfty` to the identity.
  refine HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d _
    (((homotopyPInftyToId G).hom (n + 1) (n + 2)) x) ?_
  have h := congr($((homotopyPInftyToId G).comm (n + 1)) x)
  rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl),
    prevD_eq _ (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)] at h
  simp only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, hx₀, map_zero,
    zero_add, HomologicalComplex.id_f, ModuleCat.id_apply] at h
  simp only [HomologicalComplex.iCycles_moduleCatCyclesMk, Submodule.subtype_apply]
  rw [h, add_sub_cancel_right]
  -- `K[G]` is by definition the alternating face map complex `(alternatingFaceMapComplex _).obj G`
  rfl

private lemma piToHomology_bijective : Function.Bijective (piToHomology (G := G) (n := n)) :=
  ⟨piToHomology_injective, piToHomology_surjective⟩

variable (G n) in
/-- The homotopy groups of a simplicial module `G` at the vertex `0` are the homology groups of
its alternating face map complex `C(G)`: the class of a pointed `(n + 1)`-simplex, an element of
`G_{n+1}` all of whose faces vanish, is sent to its homology class. -/
def piAddEquivAlternatingFaceMapComplexHomology :
    Additive (KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) ≃+
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology (n + 1) :=
  AddEquiv.ofBijective piToHomology piToHomology_bijective

/-- The isomorphism `π_{n+1}(G, 0) ≃+ H_{n+1}(C(G))` sends the class of a pointed simplex to the
homology class of the corresponding element of `G_{n+1}`. -/
lemma piAddEquivAlternatingFaceMapComplexHomology_mk
    (p : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) (n + 1) (0 : G _⦋0⦌))
    (c : ((alternatingFaceMapComplex (ModuleCat R)).obj G).cycles (n + 1))
    (hc : ((alternatingFaceMapComplex (ModuleCat R)).obj G).iCycles (n + 1) c =
      SSet.yonedaEquiv p.map) :
    piAddEquivAlternatingFaceMapComplexHomology G n (.ofMul (KanComplex.π.mk p)) =
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homologyπ (n + 1) c := by
  rw [piAddEquivAlternatingFaceMapComplexHomology, AddEquiv.ofBijective_apply, piToHomology_mk,
    mooreCyclesHomologyClass, HomologicalComplex.moduleCatHomologyClass_apply]
  congr 1
  apply ((alternatingFaceMapComplex (ModuleCat R)).obj G).moduleCat_iCycles_injective
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, hc, Submodule.subtype_apply,
    coe_ptSimplexEquiv_apply]

/-- The isomorphism `π_{n+1}(G, 0) ≃+ H_{n+1}(C(G))` is natural in the simplicial module `G`. -/
lemma piAddEquivAlternatingFaceMapComplexHomology_map {G' : SimplicialObject (ModuleCat.{u} R)}
    (f : G ⟶ G') (a : KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) :
    piAddEquivAlternatingFaceMapComplexHomology G' n
        (.ofMul (KanComplex.π.map (Functor.whiskerRight f (forget (ModuleCat R)))
          (map_zero (f.app _).hom) a)) =
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat R)).map f) (n + 1)
        (piAddEquivAlternatingFaceMapComplexHomology G n (.ofMul a)) := by
  induction a with | mk p
  simp only [KanComplex.π.map_mk, piAddEquivAlternatingFaceMapComplexHomology,
    AddEquiv.ofBijective_apply, piToHomology_mk, mooreCyclesHomologyClass,
    HomologicalComplex.moduleCatHomologyClass_apply,
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  -- the simplex of `p.map ≫ f` is the image under `f` of the simplex of `p.map`
  rfl

/-! ### Degree zero -/

variable (G) in
/-- The homology class in degree zero of the alternating face map complex of an element of
`G_0`. -/
private def homologyClassZero :
    G _⦋0⦌ →ₗ[R] ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology 0 :=
  ((alternatingFaceMapComplex (ModuleCat R)).obj G).moduleCatHomologyClass (m := 0) (by simp)
    LinearMap.id fun z ↦ by
      rw [HomologicalComplex.shape _ 0 0 (by simp)]
      simp

/-- Homotopic `0`-simplices have the same homology class: a homotopy restricts to an edge from
one to the other, whose boundary is their difference. -/
private lemma homologyClassZero_eq_of_homotopy
    {p q : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) 0 (0 : G _⦋0⦌)} (h : p.Homotopy q) :
    homologyClassZero G (SSet.yonedaEquiv p.map) =
      homologyClassZero G (SSet.yonedaEquiv q.map) := by
  rw [← sub_eq_zero, ← map_sub, homologyClassZero,
    HomologicalComplex.moduleCatHomologyClass_eq_zero_iff (p := 1) _ _ _ _ (by simp)]
  refine ⟨-SSet.yonedaEquiv (prodStdSimplex₁.ι 0 ≫ h.h), ?_⟩
  have h₀ : G.δ 0 (SSet.yonedaEquiv (prodStdSimplex₁.ι 0 ≫ h.h)) = SSet.yonedaEquiv q.map := by
    rw [δ_yonedaEquiv, ← Category.assoc, ← Fin.castSucc_zero, prodStdSimplex₁.δ_castSucc_ι,
      Fin.castSucc_zero, prodStdSimplex₁.yonedaEquiv_symm_codimOneSimplex_zero, h.h₁]
  have h₁ : G.δ 1 (SSet.yonedaEquiv (prodStdSimplex₁.ι 0 ≫ h.h)) = SSet.yonedaEquiv p.map := by
    rw [δ_yonedaEquiv, ← Category.assoc, ← Fin.succ_zero_eq_one, prodStdSimplex₁.δ_succ_ι,
      show ((0 : Fin 1).succ : Fin 2) = Fin.last (0 + 1) from rfl,
      prodStdSimplex₁.yonedaEquiv_symm_codimOneSimplex_last, h.h₀]
  rw [map_neg, d_apply]
  simp [Fin.sum_univ_two, h₀, h₁, sub_eq_add_neg]

/-- The homology class in degree zero of a vertex, on path components. -/
private def piZeroToHomology :
    KanComplex.π 0 (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌) →
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology 0 :=
  KanComplex.π.lift (fun p ↦ homologyClassZero G (SSet.yonedaEquiv p.map))
    fun _ _ ↦ homologyClassZero_eq_of_homotopy

private lemma piZeroToHomology_bijective : Function.Bijective (piZeroToHomology (G := G)) := by
  refine ⟨fun a b hab ↦ ?_, fun c ↦ ?_⟩
  · induction a with | mk p
    induction b with | mk q
    rw [piZeroToHomology, KanComplex.π.lift_mk, KanComplex.π.lift_mk, ← sub_eq_zero, ← map_sub,
      homologyClassZero,
      HomologicalComplex.moduleCatHomologyClass_eq_zero_iff (p := 1) _ _ _ _ (by simp)] at hab
    obtain ⟨e, he⟩ := hab
    -- The edge `e + s₀ (q - δ₁ e)` joins `q` to `p`.
    set x : G _⦋0⦌ := SSet.yonedaEquiv p.map
    set y : G _⦋0⦌ := SSet.yonedaEquiv q.map
    let e₁ : G _⦋1⦌ := e
    have he' : G.δ 0 e₁ - G.δ 1 e₁ = x - y := by
      rw [d_apply, Fin.sum_univ_two] at he
      simpa [sub_eq_add_neg] using he
    have hσ₀ := congr($(G.δ_comp_σ_self (i := (0 : Fin 1))) (y - G.δ 1 e₁))
    have hσ₁ := congr($(G.δ_comp_σ_succ (i := (0 : Fin 1))) (y - G.δ 1 e₁))
    simp only [ModuleCat.comp_apply, ModuleCat.id_apply, Fin.castSucc_zero,
      Fin.succ_zero_eq_one] at hσ₀ hσ₁
    have h₀ : G.δ 0 (e₁ + G.σ 0 (y - G.δ 1 e₁)) = SSet.yonedaEquiv p.map := by
      rw [map_add, hσ₀]
      calc G.δ 0 e₁ + (y - G.δ 1 e₁) = (G.δ 0 e₁ - G.δ 1 e₁) + y := by abel
        _ = x := by rw [he', sub_add_cancel]
    have h₁ : G.δ 1 (e₁ + G.σ 0 (y - G.δ 1 e₁)) = SSet.yonedaEquiv q.map := by
      rw [map_add, hσ₁, add_sub_cancel]
    exact (KanComplex.π.mk_eq_mk_of_homotopy
      (PtSimplex.RelStruct₀.homotopy
        { map := (SSet.yonedaEquiv.symm (e₁ + G.σ 0 (y - G.δ 1 e₁)) :
            Δ[1] ⟶ G ⋙ forget (ModuleCat R))
          δ_castSucc_map := δ_comp_yonedaEquiv_symm_eq G h₀
          δ_succ_map := δ_comp_yonedaEquiv_symm_eq G h₁
          δ_map_of_lt := fun j hj ↦ absurd hj (Fin.not_lt_zero _)
          δ_map_of_gt := fun j hj ↦ absurd hj (not_lt.2 (Fin.le_last j)) })).symm
  · have hs : Function.Surjective (homologyClassZero G) :=
      HomologicalComplex.moduleCatHomologyClass_surjective _ _ _ _ fun x _ ↦ ⟨x, rfl⟩
    obtain ⟨x, rfl⟩ := hs c
    exact ⟨KanComplex.π.mk ((PtSimplex.equiv₀ _).symm x), (KanComplex.π.lift_mk _ _ _).trans
      (congrArg _ (by rw [← PtSimplex.equiv₀_apply, Equiv.apply_symm_apply]))⟩

variable (G) in
/-- The path components of the underlying simplicial set of a simplicial module `G` are the
degree-zero homology of its alternating face map complex `C(G)`: the class of a vertex is sent to
its homology class. -/
def piZeroEquivAlternatingFaceMapComplexHomology :
    KanComplex.π 0 (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌) ≃
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology 0 :=
  Equiv.ofBijective piZeroToHomology piZeroToHomology_bijective

/-- The isomorphism `π₀(G, 0) ≃ H₀(C(G))` sends the class of a vertex to its homology class. -/
lemma piZeroEquivAlternatingFaceMapComplexHomology_mk
    (p : SSet.PtSimplex (G ⋙ forget (ModuleCat R)) 0 (0 : G _⦋0⦌))
    (c : ((alternatingFaceMapComplex (ModuleCat R)).obj G).cycles 0)
    (hc : ((alternatingFaceMapComplex (ModuleCat R)).obj G).iCycles 0 c =
      SSet.yonedaEquiv p.map) :
    piZeroEquivAlternatingFaceMapComplexHomology G (KanComplex.π.mk p) =
      ((alternatingFaceMapComplex (ModuleCat R)).obj G).homologyπ 0 c := by
  rw [piZeroEquivAlternatingFaceMapComplexHomology, Equiv.ofBijective_apply, piZeroToHomology,
    KanComplex.π.lift_mk, homologyClassZero, HomologicalComplex.moduleCatHomologyClass_apply]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, hc, LinearMap.id_apply]

/-- The isomorphism `π₀(G, 0) ≃ H₀(C(G))` is natural in the simplicial module `G`. -/
lemma piZeroEquivAlternatingFaceMapComplexHomology_map {G' : SimplicialObject (ModuleCat.{u} R)}
    (f : G ⟶ G') (a : KanComplex.π 0 (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) :
    piZeroEquivAlternatingFaceMapComplexHomology G'
        (KanComplex.π.map (Functor.whiskerRight f (forget (ModuleCat R)))
          (map_zero (f.app _).hom) a) =
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat R)).map f) 0
        (piZeroEquivAlternatingFaceMapComplexHomology G a) := by
  induction a with | mk p
  simp only [KanComplex.π.map_mk, piZeroEquivAlternatingFaceMapComplexHomology,
    Equiv.ofBijective_apply, piZeroToHomology, KanComplex.π.lift_mk, homologyClassZero,
    HomologicalComplex.moduleCatHomologyClass_apply,
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  -- the simplex of `p.map ≫ f` is the image under `f` of the simplex of `p.map`
  rfl

/-! ### The comparison with the homology of the normalized Moore complex -/

variable (G) in
/-- The isomorphism `H_k(C(G)) ≃ H_k(N(G))`, the inverse of the map induced by the inclusion of the
normalized Moore complex, a homotopy equivalence. -/
private def toNormalizedMooreComplexHomology (k : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology k ≃ₗ[R]
      ((normalizedMooreComplex (ModuleCat R)).obj G).homology k :=
  ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := G)).toHomologyIso
    k).symm.toLinearEquiv

private lemma homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology {k : ℕ}
    (x : ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology k) :
    HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) k
      (toNormalizedMooreComplexHomology G k x) = x :=
  ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := G)).toHomologyIso
    k).toLinearEquiv.apply_symm_apply x

/-- The map induced on homology by the inclusion `N(G) ⟶ C(G)` is injective. -/
private lemma homologyMap_inclusionOfMooreComplexMap_injective (k : ℕ) :
    Function.Injective (HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) k) :=
  ((homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := G)).toHomologyIso
    k).toLinearEquiv.injective

private lemma toNormalizedMooreComplexHomology_homologyMap {G' : SimplicialObject (ModuleCat.{u} R)}
    (f : G ⟶ G') {k : ℕ} (x : ((alternatingFaceMapComplex (ModuleCat R)).obj G).homology k) :
    toNormalizedMooreComplexHomology G' k
        (HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat R)).map f) k x) =
      HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat R)).map f) k
        (toNormalizedMooreComplexHomology G k x) := by
  have h : HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat R)).map f) k ≫
      HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G') k =
        HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) k ≫
          HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat R)).map f) k := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    exact congrArg (HomologicalComplex.homologyMap · k)
      ((inclusionOfMooreComplex (ModuleCat R)).naturality f)
  apply homologyMap_inclusionOfMooreComplexMap_injective (G := G') k
  rw [homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology,
    ← ModuleCat.comp_apply, h, ModuleCat.comp_apply,
    homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology]

variable (G n) in
/-- **The homotopy groups of a simplicial module are the homology groups of its normalized Moore
complex.** For a simplicial module `G`, in particular for a simplicial abelian group regarded as a
simplicial `ℤ`-module, `π_{n+1}(G, 0)` is isomorphic to `H_{n+1}(N(G))`. It is the isomorphism
`CategoryTheory.SimplicialObject.piAddEquivAlternatingFaceMapComplexHomology` followed by the
inverse of the isomorphism induced by the inclusion `N(G) ⟶ C(G)`, a homotopy equivalence. -/
def piAddEquivNormalizedMooreComplexHomology :
    Additive (KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) ≃+
      ((normalizedMooreComplex (ModuleCat R)).obj G).homology (n + 1) :=
  (piAddEquivAlternatingFaceMapComplexHomology G n).trans
    (toNormalizedMooreComplexHomology G (n + 1)).toAddEquiv

/-- Composed with the map induced by the inclusion `N(G) ⟶ C(G)`, the isomorphism
`π_{n+1}(G, 0) ≃+ H_{n+1}(N(G))` is the isomorphism `π_{n+1}(G, 0) ≃+ H_{n+1}(C(G))`. -/
lemma homologyMap_inclusionOfMooreComplexMap_piAddEquivNormalizedMooreComplexHomology
    (a : Additive (KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌))) :
    HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) (n + 1)
        (piAddEquivNormalizedMooreComplexHomology G n a) =
      piAddEquivAlternatingFaceMapComplexHomology G n a :=
  homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology _

/-- The isomorphism `π_{n+1}(G, 0) ≃+ H_{n+1}(N(G))` is natural in the simplicial module `G`. -/
lemma piAddEquivNormalizedMooreComplexHomology_map {G' : SimplicialObject (ModuleCat.{u} R)}
    (f : G ⟶ G') (a : KanComplex.π (n + 1) (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) :
    piAddEquivNormalizedMooreComplexHomology G' n
        (.ofMul (KanComplex.π.map (Functor.whiskerRight f (forget (ModuleCat R)))
          (map_zero (f.app _).hom) a)) =
      HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat R)).map f) (n + 1)
        (piAddEquivNormalizedMooreComplexHomology G n (.ofMul a)) := by
  rw [piAddEquivNormalizedMooreComplexHomology, AddEquiv.trans_apply,
    piAddEquivAlternatingFaceMapComplexHomology_map]
  exact toNormalizedMooreComplexHomology_homologyMap f _

variable (G) in
/-- The path components of the underlying simplicial set of a simplicial module `G` are the
degree-zero homology of its normalized Moore complex `N(G)`. -/
def piZeroEquivNormalizedMooreComplexHomology :
    KanComplex.π 0 (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌) ≃
      ((normalizedMooreComplex (ModuleCat R)).obj G).homology 0 :=
  (piZeroEquivAlternatingFaceMapComplexHomology G).trans
    (toNormalizedMooreComplexHomology G 0).toEquiv

/-- Composed with the map induced by the inclusion `N(G) ⟶ C(G)`, the isomorphism
`π₀(G, 0) ≃ H₀(N(G))` is the isomorphism `π₀(G, 0) ≃ H₀(C(G))`. -/
lemma homologyMap_inclusionOfMooreComplexMap_piZeroEquivNormalizedMooreComplexHomology
    (a : KanComplex.π 0 (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) :
    HomologicalComplex.homologyMap (inclusionOfMooreComplexMap G) 0
        (piZeroEquivNormalizedMooreComplexHomology G a) =
      piZeroEquivAlternatingFaceMapComplexHomology G a :=
  homologyMap_inclusionOfMooreComplexMap_toNormalizedMooreComplexHomology _

/-- The isomorphism `π₀(G, 0) ≃ H₀(N(G))` is natural in the simplicial module `G`. -/
lemma piZeroEquivNormalizedMooreComplexHomology_map {G' : SimplicialObject (ModuleCat.{u} R)}
    (f : G ⟶ G') (a : KanComplex.π 0 (G ⋙ forget (ModuleCat R)) (0 : G _⦋0⦌)) :
    piZeroEquivNormalizedMooreComplexHomology G'
        (KanComplex.π.map (Functor.whiskerRight f (forget (ModuleCat R)))
          (map_zero (f.app _).hom) a) =
      HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat R)).map f) 0
        (piZeroEquivNormalizedMooreComplexHomology G a) := by
  rw [piZeroEquivNormalizedMooreComplexHomology, Equiv.trans_apply,
    piZeroEquivAlternatingFaceMapComplexHomology_map]
  exact toNormalizedMooreComplexHomology_homologyMap f _

end CategoryTheory.SimplicialObject
