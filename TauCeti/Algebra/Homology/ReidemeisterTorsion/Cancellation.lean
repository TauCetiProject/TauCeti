/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Componentwise
public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Periodic.Basic
import TauCeti.Algebra.Homology.ModuleCat.Finrank
import TauCeti.LinearAlgebra.Basis.Basic
import TauCeti.LinearAlgebra.Determinant.Cons
import TauCeti.RingTheory.Artinian.EquivPi

/-!
# Cancelling a pair of generators of a based two-periodic complex

Let `C` be a two-periodic complex of vector spaces over a field `F` with ordered bases `c`, and
let `i` and `i' = i + 1` be its two degrees. Suppose that the entry `a` of the matrix of the
differential `d : Cᵢ → Cᵢ'` at the first basis vectors `z⁺ = c i 0` and `z⁻ = c i' 0` is nonzero.
Writing this matrix in the block form `[[a, v], [w, N]]`, Gaussian elimination cancels the pair
`(z⁺, z⁻)`: the reduced complex `D` keeps the remaining basis vectors, and its differential
`Dᵢ → Dᵢ'` is the Schur complement `N - w a⁻¹ v`. This is how the based Floer and Morse–Novikov
complexes change when two generators are born or die in a generic one-parameter family, the
return trajectories between them making up the entry `a`.

The reduced complex is described here by a chain map `φ : D ⟶ C` with bases `e` of `D`, sending
`e i l` to `c i l.succ` up to a multiple of `z⁺` and `e i' l` to `c i' l.succ` up to a multiple of
`d z⁺` (the hypotheses `hφ` and `hφ'` below). Then:

* `C` is acyclic exactly when `D` is (`HomologicalComplex.acyclic_iff_of_cancel`);
* the matrix of `D.d i i'` in the bases `e` is the Schur complement of `a` in the matrix of
  `C.d i i'` in the bases `c` (`HomologicalComplex.toMatrix_d_eq_of_cancel`);
* the torsions differ by the factor `a`, inverted when the pair is joined by the odd-to-even
  differential, and by the sign `(-1) ^ q`, where `q` is the dimension of the image of the other
  differential `D.d i' i` (`HomologicalComplex.parityTorsion_eq_of_cancel_one_zero` and
  `HomologicalComplex.parityTorsion_eq_of_cancel_zero_one`). So
  `τ(C) = (-1) ^ q · a⁻¹ · τ(D)` when `z⁺` is odd, and `τ(C) = (-1) ^ q · a · τ(D)` when `z⁺` is
  even, both sides vanishing when the complexes are not acyclic.

The proof changes the bases `c` by unitriangular matrices, which do not change the torsion, into
bases in which `C` is the direct sum of `D` and the elementary complex `z⁺ ↦ a • z⁻`. Its brackets
are then those of `D`, times `a` in the degree of `z⁻` and times the sign of moving `z⁺` past the
boundaries in its own degree.

The same identity holds componentwise over a commutative ring `A`, such as a Novikov ring, where the
torsion of a based two-periodic complex is read in a reduced Artinian ring `Q`, for instance the
total quotient ring of `A`, through a ring homomorphism `f : A →+* Q`
(`HomologicalComplex.componentwiseParityTorsion`). Suppose that `C` and `D` are based
two-periodic complexes over `A` and that `φ : D ⟶ C` satisfies the hypotheses above over `A`. The
coordinate base changes of `C`, `D` and `φ` to a field `K` along any `g : A →+* K` satisfy them over
`K`, because the coordinate maps `C.X k → Kⁿ⁽ᵏ⁾` intertwine the differentials and the chain maps
(`HomologicalComplex.matrixBaseChange_d_apply_semilinearMap`,
`HomologicalComplex.matrixBaseChangeMap_f_apply_semilinearMap`). So in each residue field `Q ⧸ m`
where the image of `a` is nonzero the torsions of the base changes differ by the image of `a`,
inverted when `z⁺` is odd, and by a sign
(`HomologicalComplex.mk_componentwiseParityTorsion_eq_of_cancel_one_zero`,
`HomologicalComplex.mk_componentwiseParityTorsion_eq_of_cancel_zero_one`). When `f a` is a unit of
`Q`, the componentwise torsions differ by `(f a)⁻¹`, respectively `f a`, and by an element `ε` of
`Q` with `ε * ε = 1`
(`HomologicalComplex.exists_componentwiseParityTorsion_eq_of_cancel_one_zero`,
`HomologicalComplex.exists_componentwiseParityTorsion_eq_of_cancel_zero_one`). In each component
where the complexes are acyclic, `ε` is necessarily `(-1) ^ q`, where `q` is the rank of the base
change of `D.d i' i` there, so `ε` need not be a global sign; in the other components both
torsions vanish and the identity does not constrain `ε`. This is the form of the birth/death
identity for the torsion of a Floer–Novikov complex over a Novikov ring: at a death the entry `a`
is `1 + b`, a unit of the Novikov ring, and the componentwise torsions of the complexes before
and after the death differ by `(1 + b)^(±1)` up to the sign `(-1) ^ q` in every field component
of the total quotient ring, including the components where both complexes are not acyclic and
both torsions vanish.

## Main results

* `HomologicalComplex.acyclic_iff_of_cancel`, `HomologicalComplex.toMatrix_d_eq_of_cancel`:
  cancellation preserves acyclicity, and the cancelled differential is the Schur complement.
* `HomologicalComplex.parityTorsion_eq_of_cancel_one_zero`,
  `HomologicalComplex.parityTorsion_eq_of_cancel_zero_one`: the torsion after cancelling a pair,
  over a field.
* `HomologicalComplex.acyclic_matrixBaseChange_iff_of_cancel`,
  `HomologicalComplex.parityTorsion_matrixBaseChange_eq_of_cancel_one_zero`,
  `HomologicalComplex.parityTorsion_matrixBaseChange_eq_of_cancel_zero_one`: the same for the
  coordinate base changes to a field of complexes over a commutative ring.
* `HomologicalComplex.mk_componentwiseParityTorsion_eq_of_cancel_one_zero`,
  `HomologicalComplex.exists_componentwiseParityTorsion_eq_of_cancel_one_zero` and their
  even-to-odd versions: the componentwise torsion after cancelling a pair.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, §3.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311.
* J. Milnor, *Whitehead torsion*, Bull. Amer. Math. Soc. 72 (1966), §3.
-/

public section

noncomputable section

open CategoryTheory Module

namespace HomologicalComplex

variable {F : Type*} [Field F]
  {C D : HomologicalComplex (ModuleCat F) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
  {c : ∀ k, Basis (Fin (n k + 1)) F (C.X k)} {e : ∀ k, Basis (Fin (n k)) F (D.X k)} {φ : D ⟶ C}

/-- The two degrees `i` and `i' = i + 1` of a two-periodic complex are distinct, and every degree
is one of them. -/
private theorem ne_and_eq_or_eq {i i' : ZMod 2} (hii' : i + 1 = i') :
    i ≠ i' ∧ ∀ k, k = i ∨ k = i' := by
  subst hii'
  revert i
  decide

section Block

variable (hc : ∀ k l, c k l.succ = (φ.f k).hom (e k l))
include hc

private theorem injective_f (k : ZMod 2) : Function.Injective (φ.f k).hom :=
  LinearMap.injective_of_linearIndependent (e k).span_eq <| by
    convert (c k).linearIndependent.comp _ (Fin.succ_injective _) using 1
    ext l
    simp [hc]

/-- The image of the differential of `C` out of degree `k` is spanned by the image of `c k 0` and
the image under `φ` of the image of the differential of `D`. -/
private theorem range_d_eq (k k' : ZMod 2) :
    LinearMap.range (C.d k k').hom =
      F ∙ (C.d k k').hom (c k 0) ⊔ (LinearMap.range (D.d k k').hom).map (φ.f k').hom := by
  rw [(c k).range_eq_span_comp, (e k).range_eq_span_comp, Submodule.map_span, ← Set.range_comp,
    ← Submodule.span_insert, ← Fin.range_cons]
  congr 2
  ext l
  induction l using Fin.cases <;> simp [hc, Hom.comm_apply]

/-- The vector `c k 0` does not lie in the image of `φ`. -/
private theorem notMem_range_f (k : ZMod 2) : c k 0 ∉ LinearMap.range (φ.f k).hom := by
  have h := (c k).linearIndependent
  rw [← Fin.cons_self_tail ⇑(c k), linearIndependent_finCons] at h
  have hr : LinearMap.range (φ.f k).hom = Submodule.span F (Set.range (Fin.tail ⇑(c k))) := by
    rw [(e k).range_eq_span_comp]
    congr 2
    ext l
    simp [Fin.tail, hc]
  rw [hr]
  exact h.2

variable {i i' : ZMod 2} {a : F} (ha : a ≠ 0) (hd : (C.d i i').hom (c i 0) = a • c i' 0)
include ha hd

omit hc in
private theorem d_apply_eq_zero : (C.d i' i).hom (c i' 0) = 0 := by
  have h := d_comp_d_apply C i i' i (c i 0)
  rw [hd, map_smul] at h
  exact (smul_eq_zero.1 h).resolve_left ha

omit ha in
/-- The boundaries of `C` into the degree of `c i' 0`: the image of the pair differential is
spanned by `a • c i' 0` and the image under `φ` of the boundaries of `D`. -/
private theorem span_cons_eq_range {p : ℕ}
    (bD : Basis (Fin p) F (LinearMap.range (D.d i i').hom)) :
    Submodule.span F (Set.range (Fin.cons (a • c i' 0) fun l ↦ (φ.f i').hom (bD l))) =
      LinearMap.range (C.d i i').hom := by
  rw [Fin.range_cons, Submodule.span_insert, Basis.span_range_map_coe, range_d_eq hc, hd]

omit hd in
private theorem linearIndependent_cons {p : ℕ}
    (bD : Basis (Fin p) F (LinearMap.range (D.d i i').hom)) :
    LinearIndependent F (Fin.cons (a • c i' 0) fun l ↦ (φ.f i').hom (bD l)) := by
  refine linearIndependent_finCons.2
    ⟨bD.linearIndependent_map_coe_basis (injective_f hc i').injOn, fun h ↦ ?_⟩
  have hle : Submodule.span F (Set.range fun l ↦ (φ.f i').hom (bD l)) ≤
      LinearMap.range (φ.f i').hom :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun l ↦ LinearMap.mem_range_self _ _)
  have := Submodule.smul_mem _ a⁻¹ (hle h)
  rw [inv_smul_smul₀ ha] at this
  exact notMem_range_f hc i' this

/-- The boundaries of `C` into the degree of `c i 0` are the image under `φ` of those of `D`. -/
private theorem span_image_eq_range {p : ℕ}
    (bD : Basis (Fin p) F (LinearMap.range (D.d i' i).hom)) :
    Submodule.span F (Set.range fun l ↦ (φ.f i).hom (bD l)) = LinearMap.range (C.d i' i).hom := by
  rw [Basis.span_range_map_coe, range_d_eq hc, d_apply_eq_zero ha hd,
    Submodule.span_singleton_eq_bot.2 rfl, bot_sup_eq]

omit ha hd in
/-- The bracket in the degree `i'` of `c i' 0`: the boundaries there are spanned by `a • c i' 0`
and the image of those of `D`, and the bracket is `a` times that of `D`. -/
private theorem torsionBracket_cons (hi : (ComplexShape.up (ZMod 2)).prev i' = i)
    (hk : (ComplexShape.up (ZMod 2)).next i' = i) (hC : C.ExactAt i') (hD : D.ExactAt i')
    {p q : ℕ} (bD₁ : Basis (Fin p) F (LinearMap.range (D.d i i').hom))
    (bD₀ : Basis (Fin q) F (LinearMap.range (D.d i' i).hom)) (sD : Fin q → D.X i')
    (hsD : ∀ l, (D.d i' i).hom (sD l) = bD₀ l)
    (b₁ : Basis (Fin (p + 1)) F (LinearMap.range (C.d i i').hom))
    (hb₁ : (fun l ↦ (b₁ l : C.X i')) = Fin.cons (a • c i' 0) fun l ↦ (φ.f i').hom (bD₁ l))
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d i' i).hom))
    (hs : ∀ l, (C.d i' i).hom ((φ.f i').hom (sD l)) = b₀ l) :
    torsionBracket c hi hk hC b₁ b₀ (fun l ↦ (φ.f i').hom (sD l)) hs =
      a * torsionBracket e hi hk hD bD₁ bD₀ sD hsD := by
  have hn' := eq_add_of_exactAt e hi hk hD bD₁ bD₀
  have hn : n i' + 1 = p + 1 + q := by omega
  rw [torsionBracket_eq_det_append c hi hk hC _ _ _ _ hn,
    torsionBracket_eq_det_append e hi hk hD _ _ _ _ hn', hb₁,
    (c i').det_append_cons_smul_comp (e i') (hc i') a _ _ hn hn']

omit ha hd in
/-- The bracket in the degree `i` of `c i 0`: the lifts there are `c i 0` followed by the image
of lifts in `D`, and the bracket is `(-1) ^ q` times that of `D`, `q` being the dimension of the
boundaries. -/
private theorem torsionBracket_image (hi : (ComplexShape.up (ZMod 2)).prev i = i')
    (hk : (ComplexShape.up (ZMod 2)).next i = i') (hC : C.ExactAt i) (hD : D.ExactAt i)
    {p q : ℕ} (bD₀ : Basis (Fin q) F (LinearMap.range (D.d i' i).hom))
    (bD₁ : Basis (Fin p) F (LinearMap.range (D.d i i').hom)) (sD : Fin p → D.X i)
    (hsD : ∀ l, (D.d i i').hom (sD l) = bD₁ l)
    (b₀ : Basis (Fin q) F (LinearMap.range (C.d i' i).hom))
    (hb₀ : (fun l ↦ (b₀ l : C.X i)) = fun l ↦ (φ.f i).hom (bD₀ l))
    (b₁ : Basis (Fin (p + 1)) F (LinearMap.range (C.d i i').hom))
    (hs : ∀ l, (C.d i i').hom
      ((Fin.cons (c i 0) (fun l ↦ (φ.f i).hom (sD l)) : Fin (p + 1) → C.X i) l) = b₁ l) :
    torsionBracket c hi hk hC b₀ b₁ (Fin.cons (c i 0) fun l ↦ (φ.f i).hom (sD l)) hs =
      (-1) ^ q * torsionBracket e hi hk hD bD₀ bD₁ sD hsD := by
  have hn' := eq_add_of_exactAt e hi hk hD bD₀ bD₁
  have hn : n i + 1 = q + (p + 1) := by omega
  rw [torsionBracket_eq_det_append c hi hk hC _ _ _ _ hn,
    torsionBracket_eq_det_append e hi hk hD _ _ _ _ hn', hb₀,
    (c i).det_append_cons_comp (e i) (hc i) _ _ hn hn']

private theorem acyclic_iff_of_block (hii' : i + 1 = i') : C.Acyclic ↔ D.Acyclic := by
  have h₁ : finrank F (LinearMap.range (C.d i i').hom) =
      finrank F (LinearMap.range (D.d i i').hom) + 1 := by
    rw [← span_cons_eq_range hc hd (chosenBoundaryBasis D e i i'),
      finrank_span_eq_card (linearIndependent_cons hc ha _), Fintype.card_fin]
  have h₂ : finrank F (LinearMap.range (C.d i' i).hom) =
      finrank F (LinearMap.range (D.d i' i).hom) := by
    rw [← span_image_eq_range hc ha hd (chosenBoundaryBasis D e i' i),
      finrank_span_eq_card (Basis.linearIndependent_map_coe_basis _ (injective_f hc i).injOn),
      Fintype.card_fin]
  have hii : i' + 1 = i := by rw [← hii', add_assoc, CharTwo.add_self_eq_zero, add_zero]
  -- In either degree `j`, with `j'` the other one, exactness compares the sum of the dimensions of
  -- the two boundary spaces with that of `C.X j` or `D.X j`, and all of these drop by one.
  have key {j j' : ZMod 2} (hjj' : j + 1 = j') (hj'j : j' + 1 = j)
      (h : j = i ∧ j' = i' ∨ j = i' ∧ j' = i) : C.ExactAt j ↔ D.ExactAt j := by
    have := Module.Finite.of_basis (c j)
    have := Module.Finite.of_basis (e j)
    rw [exactAt_iff_finrank_add_finrank C ((ComplexShape.up _).prev_eq' hj'j)
      ((ComplexShape.up _).next_eq' hjj'), exactAt_iff_finrank_add_finrank D
      ((ComplexShape.up _).prev_eq' hj'j) ((ComplexShape.up _).next_eq' hjj'),
      finrank_eq_card_basis (c j), finrank_eq_card_basis (e j), Fintype.card_fin, Fintype.card_fin]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  refine forall_congr' fun j ↦ ?_
  obtain h | h := (ne_and_eq_or_eq hii').2 j
  · exact key (h ▸ hii') (h ▸ hii) (.inl ⟨h, rfl⟩)
  · exact key (h ▸ hii) (h ▸ hii') (.inr ⟨h, rfl⟩)

/-- The brackets of `C` in both degrees, for boundary bases and lifts built from the chosen ones of
`D` with `φ`: in the degree `i'` of `c i' 0` the bracket is `a` times that of `D`, and in the degree
`i` of `c i 0` it is `(-1) ^ q` times that of `D`, `q` being the dimension of the image of
`D.d i' i`. -/
private theorem exists_torsionBracket_eq (hC : C.Acyclic) (hD : D.Acyclic) :
    ∃ (b₁ : Basis (Fin (finrank F (LinearMap.range (D.d i i').hom) + 1)) F
        (LinearMap.range (C.d i i').hom))
      (b₀ : Basis (Fin (finrank F (LinearMap.range (D.d i' i).hom))) F
        (LinearMap.range (C.d i' i).hom))
      (s₀ : Fin (finrank F (LinearMap.range (D.d i' i).hom)) → C.X i')
      (hs₀ : ∀ l, (C.d i' i).hom (s₀ l) = b₀ l)
      (s₁ : Fin (finrank F (LinearMap.range (D.d i i').hom) + 1) → C.X i)
      (hs₁ : ∀ l, (C.d i i').hom (s₁ l) = b₁ l),
      (∀ (hi : (ComplexShape.up (ZMod 2)).prev i' = i)
        (hk : (ComplexShape.up (ZMod 2)).next i' = i),
        torsionBracket c hi hk (hC i') b₁ b₀ s₀ hs₀ =
          a * torsionBracket e hi hk (hD i') (chosenBoundaryBasis D e i i')
            (chosenBoundaryBasis D e i' i) (chosenBoundaryLift D e i' i)
            (chosenBoundaryLift_spec D e i' i)) ∧
      ∀ (hi : (ComplexShape.up (ZMod 2)).prev i = i')
        (hk : (ComplexShape.up (ZMod 2)).next i = i'),
        torsionBracket c hi hk (hC i) b₀ b₁ s₁ hs₁ =
          (-1) ^ finrank F (LinearMap.range (D.d i' i).hom) *
            torsionBracket e hi hk (hD i) (chosenBoundaryBasis D e i' i)
              (chosenBoundaryBasis D e i i') (chosenBoundaryLift D e i i')
              (chosenBoundaryLift_spec D e i i') := by
  let bD₀ := chosenBoundaryBasis D e i' i
  let bD₁ := chosenBoundaryBasis D e i i'
  let sD₀ := chosenBoundaryLift D e i' i
  let sD₁ := chosenBoundaryLift D e i i'
  let b₁ := Basis.ofSpanEq (linearIndependent_cons hc ha bD₁) (span_cons_eq_range hc hd bD₁)
  let b₀ := Basis.ofSpanEq (bD₀.linearIndependent_map_coe_basis (injective_f hc i).injOn)
    (span_image_eq_range hc ha hd bD₀)
  have hs₀ (l) : (C.d i' i).hom ((φ.f i').hom (sD₀ l)) = b₀ l := by
    simp [b₀, sD₀, bD₀, Hom.comm_apply]
  have hs₁ (l) : (C.d i i').hom ((Fin.cons (c i 0) fun l ↦ (φ.f i).hom (sD₁ l) :
      Fin _ → C.X i) l) = b₁ l := by
    induction l using Fin.cases <;> simp [b₁, sD₁, bD₁, hd, Hom.comm_apply]
  refine ⟨b₁, b₀, _, hs₀, _, hs₁, fun hi hk ↦ ?_, fun hi hk ↦ ?_⟩
  · exact torsionBracket_cons hc hi hk (hC i') (hD i') bD₁ bD₀ sD₀
      (chosenBoundaryLift_spec D e i' i) b₁ (funext fun l ↦ by simp [b₁]) b₀ hs₀
  · exact torsionBracket_image hc hi hk (hC i) (hD i) bD₀ bD₁ sD₁
      (chosenBoundaryLift_spec D e i i') b₀ (funext fun l ↦ by simp [b₀]) b₁ hs₁

end Block

section BlockOneZero

variable (hc : ∀ k l, c k l.succ = (φ.f k).hom (e k l)) {a : F} (ha : a ≠ 0)
  (hd : (C.d 1 0).hom (c 1 0) = a • c 0 0)
include hc ha hd

private theorem parityTorsion_eq_of_block_one_zero :
    C.parityTorsion c =
      (-1) ^ finrank F (LinearMap.range (D.d 0 1).hom) * a⁻¹ * D.parityTorsion e := by
  have hii' : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases hD : D.Acyclic
  swap
  · rw [parityTorsion_of_not_acyclic D e hD, parityTorsion_of_not_acyclic C c
      (by rwa [acyclic_iff_of_block hc ha hd hii']), mul_zero]
  have hC := (acyclic_iff_of_block hc ha hd hii').2 hD
  obtain ⟨b₀, b₁, s₀, hs₀, s₁, hs₁, h₀, h₁⟩ := exists_torsionBracket_eq hc ha hd hC hD
  rw [parityTorsion_eq hC b₀ b₁ s₀ hs₀ s₁ hs₁, parityTorsion_eq hD _ _ _
    (chosenBoundaryLift_spec D e 0 1) _ (chosenBoundaryLift_spec D e 1 0), h₀, h₁, mul_inv]
  ring

end BlockOneZero

section BlockZeroOne

variable (hc : ∀ k l, c k l.succ = (φ.f k).hom (e k l)) {a : F} (ha : a ≠ 0)
  (hd : (C.d 0 1).hom (c 0 0) = a • c 1 0)
include hc ha hd

private theorem parityTorsion_eq_of_block_zero_one :
    C.parityTorsion c =
      (-1) ^ finrank F (LinearMap.range (D.d 1 0).hom) * a * D.parityTorsion e := by
  have hii' : (0 : ZMod 2) + 1 = 1 := by decide
  by_cases hD : D.Acyclic
  swap
  · rw [parityTorsion_of_not_acyclic D e hD, parityTorsion_of_not_acyclic C c
      (by rwa [acyclic_iff_of_block hc ha hd hii']), mul_zero]
  have hC := (acyclic_iff_of_block hc ha hd hii').2 hD
  obtain ⟨b₁, b₀, s₁, hs₁, s₀, hs₀, h₁, h₀⟩ := exists_torsionBracket_eq hc ha hd hC hD
  rw [parityTorsion_eq hC b₀ b₁ s₀ hs₀ s₁ hs₁, parityTorsion_eq hD _ _ _
    (chosenBoundaryLift_spec D e 0 1) _ (chosenBoundaryLift_spec D e 1 0), h₀, h₁, mul_inv,
    ← inv_pow, inv_neg_one]
  ring

end BlockZeroOne

section Cancel

variable {i i' : ZMod 2}
  (hφ : ∀ l, (φ.f i).hom (e i l) - c i l.succ ∈ F ∙ c i 0)
  (hφ' : ∀ l, (φ.f i').hom (e i' l) - c i' l.succ ∈ F ∙ (C.d i i').hom (c i 0))
  (ha : (c i').repr ((C.d i i').hom (c i 0)) 0 ≠ 0)
include hφ hφ' ha

/-- The bases adapted to the cancellation: `c i 0` and `a⁻¹ • d (c i 0)` followed by the images
of the bases `e`. They differ from `c` by unitriangular changes of basis. -/
private theorem exists_adapted (hii' : i + 1 = i') : ∃ c' : ∀ k, Basis (Fin (n k + 1)) F (C.X k),
    (∀ k l, c' k l.succ = (φ.f k).hom (e k l)) ∧
      (C.d i i').hom (c' i 0) = (c i').repr ((C.d i i').hom (c i 0)) 0 • c' i' 0 ∧
      ∀ k, (c k).det (c' k) = 1 := by
  set a := (c i').repr ((C.d i i').hom (c i 0)) 0
  set x := a⁻¹ • (C.d i i').hom (c i 0)
  choose t ht using fun l ↦ Submodule.mem_span_singleton.1 (hφ l)
  choose s hs using fun l ↦ Submodule.mem_span_singleton.1 (hφ' l)
  have hdet : (c i).det (Fin.cons (c i 0) fun l ↦ (φ.f i).hom (e i l)) = 1 := by
    have : (fun l ↦ (φ.f i).hom (e i l)) = fun l ↦ c i l.succ + t l • c i 0 := by
      ext l; rw [ht]; abel
    rw [this, Module.Basis.det_cons_add_smul]
    simp
  have hdet' : (c i').det (Fin.cons x fun l ↦ (φ.f i').hom (e i' l)) = 1 := by
    have : (fun l ↦ (φ.f i').hom (e i' l)) = fun l ↦ c i' l.succ + (s l * a) • x := by
      ext l; rw [mul_smul, smul_inv_smul₀ ha, hs]; abel
    rw [this, Module.Basis.det_cons_add_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
      inv_mul_cancel₀ ha]
  let β := Basis.mk ((c i).is_basis_iff_det.2 (hdet ▸ isUnit_one)).1
    ((c i).is_basis_iff_det.2 (hdet ▸ isUnit_one)).2.ge
  let β' := Basis.mk ((c i').is_basis_iff_det.2 (hdet' ▸ isUnit_one)).1
    ((c i').is_basis_iff_det.2 (hdet' ▸ isUnit_one)).2.ge
  have hne : i ≠ i' := (ne_and_eq_or_eq hii').1
  have hβ : Function.update (Function.update c i β) i' β' i = β := by
    rw [Function.update_of_ne hne, Function.update_self]
  have hβ' : Function.update (Function.update c i β) i' β' i' = β' := Function.update_self ..
  refine ⟨Function.update (Function.update c i β) i' β', fun k l ↦ ?_, ?_, fun k ↦ ?_⟩
  · obtain rfl | rfl := (ne_and_eq_or_eq hii').2 k
    · simp [hβ, β]
    · simp [β']
  · rw [hβ, hβ']
    simp [β, β', x, smul_inv_smul₀ ha]
  · obtain rfl | rfl := (ne_and_eq_or_eq hii').2 k
    · rw [hβ, Basis.coe_mk, hdet]
    · rw [hβ', Basis.coe_mk, hdet']

/-- **Cancelling a pair of generators preserves acyclicity.** Let `φ : D ⟶ C` send each basis
vector `e i l` to `c i l.succ` up to a multiple of `c i 0`, and each `e i' l` to `c i' l.succ` up
to a multiple of `d (c i 0)`, where the coordinate of `d (c i 0)` along `c i' 0` is nonzero. Then
`C` is acyclic exactly when `D` is. -/
theorem acyclic_iff_of_cancel : C.Acyclic ↔ D.Acyclic := by
  have hii' : i + 1 = i' := by
    by_contra h
    exact ha (by rw [C.shape i i' h]; simp)
  obtain ⟨c', hc', hd', -⟩ := exists_adapted hφ hφ' ha hii'
  exact acyclic_iff_of_block hc' ha hd' hii'

omit hφ in
/-- In the degree `i'`, the coordinates of a vector of `D` in the basis `e i'` are read off the
coordinates of its image under `φ`, corrected along `d (c i 0)`. -/
private theorem repr_eq_of_cancel (y : D.X i') (r : Fin (n i')) :
    (e i').repr y r = (c i').repr ((φ.f i').hom y) r.succ -
      (c i').repr ((C.d i i').hom (c i 0)) r.succ *
        ((c i').repr ((C.d i i').hom (c i 0)) 0)⁻¹ * (c i').repr ((φ.f i').hom y) 0 := by
  choose s hs using fun l ↦ Submodule.mem_span_singleton.1 (hφ' l)
  set A := (c i').repr ((C.d i i').hom (c i 0)) 0
  set X := (c i').repr ((C.d i i').hom (c i 0)) r.succ
  have h := (e i').ext (f₁ := (e i').coord r) (f₂ := (c i').coord r.succ ∘ₗ (φ.f i').hom -
    (X * A⁻¹) • (c i').coord 0 ∘ₗ (φ.f i').hom) fun l ↦ by
    have hφe : (φ.f i').hom (e i' l) = c i' l.succ + s l • (C.d i i').hom (c i 0) := by
      rw [hs]; abel
    have h₀ : (c i').repr (c i' l.succ) 0 = 0 := by simp
    have h₁ : (c i').repr (c i' l.succ) r.succ = (e i').repr (e i' l) r := by
      simp [Finsupp.single_apply, Fin.succ_inj]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, Basis.coord_apply,
      hφe, map_add, map_smul, smul_eq_mul, h₀, h₁]
    field_simp
    ring
  simpa [mul_assoc] using LinearMap.congr_fun h y

/-- **The cancelled differential is the Schur complement.** In the bases `e`, the matrix of the
differential `D.d i i'` is the Schur complement `N - w a⁻¹ v` of the entry `a` of the matrix of
`C.d i i'` in the bases `c` at the pair `(c i 0, c i' 0)`, where `v` is the rest of its row, `w`
the rest of its column and `N` the remaining block. Here `φ` and the bases are as in
`HomologicalComplex.acyclic_iff_of_cancel`. -/
theorem toMatrix_d_eq_of_cancel :
    LinearMap.toMatrix (e i) (e i') (D.d i i').hom = Matrix.of fun r k ↦
      LinearMap.toMatrix (c i) (c i') (C.d i i').hom r.succ k.succ -
        LinearMap.toMatrix (c i) (c i') (C.d i i').hom r.succ 0 *
          (LinearMap.toMatrix (c i) (c i') (C.d i i').hom 0 0)⁻¹ *
            LinearMap.toMatrix (c i) (c i') (C.d i i').hom 0 k.succ := by
  choose t ht using fun l ↦ Submodule.mem_span_singleton.1 (hφ l)
  refine Matrix.ext fun r k ↦ ?_
  have hφe : (φ.f i).hom (e i k) = c i k.succ + t k • c i 0 := by rw [ht]; abel
  have h := repr_eq_of_cancel hφ' ha ((D.d i i').hom (e i k)) r
  have hcomm : (φ.f i').hom ((D.d i i').hom (e i k)) = (C.d i i').hom ((φ.f i).hom (e i k)) :=
    (Hom.comm_apply φ i i' _).symm
  rw [hcomm, hφe] at h
  simp only [LinearMap.toMatrix_apply, Matrix.of_apply, h, map_add, map_smul, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul]
  set A := (c i').repr ((C.d i i').hom (c i 0)) 0
  field_simp
  ring

end Cancel

/-- **The torsion after cancelling a pair joined by the odd-to-even differential.** Let `φ : D ⟶ C`
send each `e 1 l` to `c 1 l.succ` up to a multiple of `c 1 0`, and each `e 0 l` to `c 0 l.succ` up
to a multiple of `d (c 1 0)`, and let the coordinate `a` of `d (c 1 0)` along `c 0 0` be nonzero.
Then `τ(C) = (-1) ^ q · a⁻¹ · τ(D)`, where `q` is the dimension of the image of the even-to-odd
differential of `D`. Both sides vanish when the complexes are not acyclic. -/
theorem parityTorsion_eq_of_cancel_one_zero
    (hφ : ∀ l, (φ.f 1).hom (e 1 l) - c 1 l.succ ∈ F ∙ c 1 0)
    (hφ' : ∀ l, (φ.f 0).hom (e 0 l) - c 0 l.succ ∈ F ∙ (C.d 1 0).hom (c 1 0))
    (ha : (c 0).repr ((C.d 1 0).hom (c 1 0)) 0 ≠ 0) :
    C.parityTorsion c = (-1) ^ finrank F (LinearMap.range (D.d 0 1).hom) *
      ((c 0).repr ((C.d 1 0).hom (c 1 0)) 0)⁻¹ * D.parityTorsion e := by
  obtain ⟨c', hc', hd', hdet⟩ := exists_adapted hφ hφ' ha (by decide : (1 : ZMod 2) + 1 = 0)
  rw [← parityTorsion_eq_of_block_one_zero hc' ha hd', parityTorsion_eq_mul_det c c', hdet, hdet]
  simp

/-- **The torsion after cancelling a pair joined by the even-to-odd differential.** Let `φ : D ⟶ C`
send each `e 0 l` to `c 0 l.succ` up to a multiple of `c 0 0`, and each `e 1 l` to `c 1 l.succ` up
to a multiple of `d (c 0 0)`, and let the coordinate `a` of `d (c 0 0)` along `c 1 0` be nonzero.
Then `τ(C) = (-1) ^ q · a · τ(D)`, where `q` is the dimension of the image of the odd-to-even
differential of `D`. Both sides vanish when the complexes are not acyclic. -/
theorem parityTorsion_eq_of_cancel_zero_one
    (hφ : ∀ l, (φ.f 0).hom (e 0 l) - c 0 l.succ ∈ F ∙ c 0 0)
    (hφ' : ∀ l, (φ.f 1).hom (e 1 l) - c 1 l.succ ∈ F ∙ (C.d 0 1).hom (c 0 0))
    (ha : (c 1).repr ((C.d 0 1).hom (c 0 0)) 0 ≠ 0) :
    C.parityTorsion c = (-1) ^ finrank F (LinearMap.range (D.d 1 0).hom) *
      (c 1).repr ((C.d 0 1).hom (c 0 0)) 0 * D.parityTorsion e := by
  obtain ⟨c', hc', hd', hdet⟩ := exists_adapted hφ hφ' ha (by decide : (0 : ZMod 2) + 1 = 1)
  rw [← parityTorsion_eq_of_block_zero_one hc' ha hd', parityTorsion_eq_mul_det c c', hdet, hdet]
  simp

end HomologicalComplex

namespace HomologicalComplex

section Componentwise

/-! ### Cancellation over a commutative ring, in each field component -/

variable {A : Type*} [CommRing A]
  {C D : HomologicalComplex (ModuleCat A) (ComplexShape.up (ZMod 2))} {n : ZMod 2 → ℕ}
  {c : ∀ k, Basis (Fin (n k + 1)) A (C.X k)} {e : ∀ k, Basis (Fin (n k)) A (D.X k)} {φ : D ⟶ C}

section Field

variable {K : Type*} [Field K] (g : A →+* K) {i i' : ZMod 2}
  (hφ : ∀ l, (φ.f i).hom (e i l) - c i l.succ ∈ A ∙ c i 0)
  (hφ' : ∀ l, (φ.f i').hom (e i' l) - c i' l.succ ∈ A ∙ (C.d i i').hom (c i 0))

include hφ in
/-- The first cancellation hypothesis passes to the coordinate base changes along `g`. -/
private theorem matrixBaseChangeMap_sub_mem_span_basis (l : Fin (n i)) :
    ((matrixBaseChangeMap c g e φ).f i).hom (D.matrixBaseChangeBasis e g i l) -
        C.matrixBaseChangeBasis c g i l.succ ∈ K ∙ C.matrixBaseChangeBasis c g i 0 := by
  rw [← (e i).semilinearMap_apply_self g _ l, matrixBaseChangeMap_f_apply_semilinearMap,
    ← (c i).semilinearMap_apply_self g _ l.succ, ← (c i).semilinearMap_apply_self g _ 0,
    ← map_sub]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (hφ l)
  exact Submodule.mem_span_singleton.2 ⟨g t, by rw [← ht, map_smulₛₗ]⟩

include hφ' in
/-- The second cancellation hypothesis passes to the coordinate base changes along `g`. -/
private theorem matrixBaseChangeMap_sub_mem_span_d (l : Fin (n i')) :
    ((matrixBaseChangeMap c g e φ).f i').hom (D.matrixBaseChangeBasis e g i' l) -
        C.matrixBaseChangeBasis c g i' l.succ ∈
      K ∙ ((C.matrixBaseChange c g).d i i').hom (C.matrixBaseChangeBasis c g i 0) := by
  rw [← (e i').semilinearMap_apply_self g _ l, matrixBaseChangeMap_f_apply_semilinearMap,
    ← (c i').semilinearMap_apply_self g _ l.succ, ← (c i).semilinearMap_apply_self g _ 0,
    matrixBaseChange_d_apply_semilinearMap, ← map_sub]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (hφ' l)
  exact Submodule.mem_span_singleton.2 ⟨g t, by rw [← ht, map_smulₛₗ]⟩

/-- The entry of the matrix of the differential of the coordinate base change at the cancelled pair
is the image under `g` of the corresponding entry for `C`. -/
private theorem repr_matrixBaseChange_d_basis :
    (C.matrixBaseChangeBasis c g i').repr
        (((C.matrixBaseChange c g).d i i').hom (C.matrixBaseChangeBasis c g i 0)) 0 =
      g ((c i').repr ((C.d i i').hom (c i 0)) 0) := by
  rw [← (c i).semilinearMap_apply_self g _ 0, matrixBaseChange_d_apply_semilinearMap,
    Basis.repr_semilinearMap_apply]

include hφ hφ' in
/-- **Cancellation preserves acyclicity in every field component.** Let `φ : D ⟶ C` satisfy the
cancellation hypotheses of `HomologicalComplex.acyclic_iff_of_cancel` over the commutative ring
`A`, and let `g : A →+* K` be a ring homomorphism into a field which does not kill the entry of the
differential at the cancelled pair. Then the coordinate base changes of `C` and `D` along `g` are
acyclic together. -/
theorem acyclic_matrixBaseChange_iff_of_cancel
    (ha : g ((c i').repr ((C.d i i').hom (c i 0)) 0) ≠ 0) :
    (C.matrixBaseChange c g).Acyclic ↔ (D.matrixBaseChange e g).Acyclic :=
  acyclic_iff_of_cancel (matrixBaseChangeMap_sub_mem_span_basis g hφ)
    (matrixBaseChangeMap_sub_mem_span_d g hφ') (by rwa [repr_matrixBaseChange_d_basis])

end Field

section OneZero

variable (hφ : ∀ l, (φ.f 1).hom (e 1 l) - c 1 l.succ ∈ A ∙ c 1 0)
  (hφ' : ∀ l, (φ.f 0).hom (e 0 l) - c 0 l.succ ∈ A ∙ (C.d 1 0).hom (c 1 0))
include hφ hφ'

/-- **The torsion after cancelling a pair joined by the odd-to-even differential, over a ring.**
Let `φ : D ⟶ C` satisfy the hypotheses of `HomologicalComplex.parityTorsion_eq_of_cancel_one_zero`
over the commutative ring `A`, with `a` the entry of the matrix of `C.d 1 0` at the cancelled pair,
and let `g : A →+* K` be a ring homomorphism into a field with `g a ≠ 0`. Then the torsions of the
coordinate base changes along `g` satisfy `τ(C) = (-1) ^ q · (g a)⁻¹ · τ(D)`, where `q` is the
dimension of the image of the base change of `D.d 0 1`. -/
theorem parityTorsion_matrixBaseChange_eq_of_cancel_one_zero {K : Type*} [Field K] (g : A →+* K)
    (ha : g ((c 0).repr ((C.d 1 0).hom (c 1 0)) 0) ≠ 0) :
    (C.matrixBaseChange c g).parityTorsion (C.matrixBaseChangeBasis c g) =
      (-1) ^ finrank K (LinearMap.range ((D.matrixBaseChange e g).d 0 1).hom) *
        (g ((c 0).repr ((C.d 1 0).hom (c 1 0)) 0))⁻¹ *
          (D.matrixBaseChange e g).parityTorsion (D.matrixBaseChangeBasis e g) := by
  rw [← repr_matrixBaseChange_d_basis] at ha ⊢
  exact parityTorsion_eq_of_cancel_one_zero (matrixBaseChangeMap_sub_mem_span_basis g hφ)
    (matrixBaseChangeMap_sub_mem_span_d g hφ') ha

variable {Q : Type*} [CommRing Q] [IsArtinianRing Q] [IsReduced Q] (f : A →+* Q)

attribute [local instance] Ideal.Quotient.field

/-- **The componentwise torsion after cancelling a pair joined by the odd-to-even differential.**
Let `φ : D ⟶ C` satisfy the hypotheses of `HomologicalComplex.parityTorsion_eq_of_cancel_one_zero`
over the commutative ring `A`, with `a` the entry of the matrix of `C.d 1 0` at the cancelled pair.
In every residue field `Q ⧸ m` of the reduced Artinian ring `Q` where the image of `f a` is
nonzero, the components of the componentwise torsions along `f` satisfy
`τ(C) = (-1) ^ q · (f a)⁻¹ · τ(D)`, where `q` is the dimension of the image of the base change of
`D.d 0 1` to `Q ⧸ m`. -/
theorem mk_componentwiseParityTorsion_eq_of_cancel_one_zero (m : MaximalSpectrum Q)
    (ha : Ideal.Quotient.mk m.asIdeal (f ((c 0).repr ((C.d 1 0).hom (c 1 0)) 0)) ≠ 0) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseParityTorsion c f) =
      (-1) ^ finrank (Q ⧸ m.asIdeal) (LinearMap.range
          ((D.matrixBaseChange e ((Ideal.Quotient.mk m.asIdeal).comp f)).d 0 1).hom) *
        (Ideal.Quotient.mk m.asIdeal (f ((c 0).repr ((C.d 1 0).hom (c 1 0)) 0)))⁻¹ *
          Ideal.Quotient.mk m.asIdeal (D.componentwiseParityTorsion e f) := by
  rw [mk_componentwiseParityTorsion, mk_componentwiseParityTorsion]
  exact parityTorsion_matrixBaseChange_eq_of_cancel_one_zero hφ hφ' _ ha

/-- **The componentwise torsion after cancelling a pair joined by the odd-to-even differential,
in the whole reduced Artinian ring.** Let `φ : D ⟶ C` satisfy the hypotheses of
`HomologicalComplex.parityTorsion_eq_of_cancel_one_zero` over the commutative ring `A`, and let the
entry `a` of the matrix of `C.d 1 0` at the cancelled pair map to a unit of `Q`. Then
`τ(C) = ε · (f a)⁻¹ · τ(D)` for the componentwise torsions along `f` and some `ε : Q` with
`ε * ε = 1`, so that `ε` is `±1` in each residue field of `Q`. In each residue field where the
complexes are acyclic, `HomologicalComplex.mk_componentwiseParityTorsion_eq_of_cancel_one_zero`
forces this sign to be `(-1) ^ q`; in the other residue fields both torsions vanish and `ε` is
unconstrained there. -/
theorem exists_componentwiseParityTorsion_eq_of_cancel_one_zero
    (ha : IsUnit (f ((c 0).repr ((C.d 1 0).hom (c 1 0)) 0))) :
    ∃ ε : Q, ε * ε = 1 ∧
      C.componentwiseParityTorsion c f = ε * ↑ha.unit⁻¹ * D.componentwiseParityTorsion e f := by
  simp_rw [mul_assoc]
  exact IsArtinianRing.exists_mul_self_eq_one_and_eq_mul _ fun m ↦
    (mk_componentwiseParityTorsion_eq_of_cancel_one_zero hφ hφ' f m
      (ha.map (Ideal.Quotient.mk m.asIdeal)).ne_zero).trans <| by
        rw [mul_assoc, map_mul, map_units_inv, IsUnit.unit_spec]

end OneZero

section ZeroOne

variable (hφ : ∀ l, (φ.f 0).hom (e 0 l) - c 0 l.succ ∈ A ∙ c 0 0)
  (hφ' : ∀ l, (φ.f 1).hom (e 1 l) - c 1 l.succ ∈ A ∙ (C.d 0 1).hom (c 0 0))
include hφ hφ'

/-- **The torsion after cancelling a pair joined by the even-to-odd differential, over a ring.**
Let `φ : D ⟶ C` satisfy the hypotheses of `HomologicalComplex.parityTorsion_eq_of_cancel_zero_one`
over the commutative ring `A`, with `a` the entry of the matrix of `C.d 0 1` at the cancelled pair,
and let `g : A →+* K` be a ring homomorphism into a field with `g a ≠ 0`. Then the torsions of the
coordinate base changes along `g` satisfy `τ(C) = (-1) ^ q · g a · τ(D)`, where `q` is the
dimension of the image of the base change of `D.d 1 0`. -/
theorem parityTorsion_matrixBaseChange_eq_of_cancel_zero_one {K : Type*} [Field K] (g : A →+* K)
    (ha : g ((c 1).repr ((C.d 0 1).hom (c 0 0)) 0) ≠ 0) :
    (C.matrixBaseChange c g).parityTorsion (C.matrixBaseChangeBasis c g) =
      (-1) ^ finrank K (LinearMap.range ((D.matrixBaseChange e g).d 1 0).hom) *
        g ((c 1).repr ((C.d 0 1).hom (c 0 0)) 0) *
          (D.matrixBaseChange e g).parityTorsion (D.matrixBaseChangeBasis e g) := by
  rw [← repr_matrixBaseChange_d_basis] at ha ⊢
  exact parityTorsion_eq_of_cancel_zero_one (matrixBaseChangeMap_sub_mem_span_basis g hφ)
    (matrixBaseChangeMap_sub_mem_span_d g hφ') ha

variable {Q : Type*} [CommRing Q] [IsArtinianRing Q] [IsReduced Q] (f : A →+* Q)

attribute [local instance] Ideal.Quotient.field

/-- **The componentwise torsion after cancelling a pair joined by the even-to-odd differential.**
Let `φ : D ⟶ C` satisfy the hypotheses of `HomologicalComplex.parityTorsion_eq_of_cancel_zero_one`
over the commutative ring `A`, with `a` the entry of the matrix of `C.d 0 1` at the cancelled pair.
In every residue field `Q ⧸ m` of the reduced Artinian ring `Q` where the image of `f a` is
nonzero, the components of the componentwise torsions along `f` satisfy
`τ(C) = (-1) ^ q · f a · τ(D)`, where `q` is the dimension of the image of the base change of
`D.d 1 0` to `Q ⧸ m`. -/
theorem mk_componentwiseParityTorsion_eq_of_cancel_zero_one (m : MaximalSpectrum Q)
    (ha : Ideal.Quotient.mk m.asIdeal (f ((c 1).repr ((C.d 0 1).hom (c 0 0)) 0)) ≠ 0) :
    Ideal.Quotient.mk m.asIdeal (C.componentwiseParityTorsion c f) =
      (-1) ^ finrank (Q ⧸ m.asIdeal) (LinearMap.range
          ((D.matrixBaseChange e ((Ideal.Quotient.mk m.asIdeal).comp f)).d 1 0).hom) *
        Ideal.Quotient.mk m.asIdeal (f ((c 1).repr ((C.d 0 1).hom (c 0 0)) 0)) *
          Ideal.Quotient.mk m.asIdeal (D.componentwiseParityTorsion e f) := by
  rw [mk_componentwiseParityTorsion, mk_componentwiseParityTorsion]
  exact parityTorsion_matrixBaseChange_eq_of_cancel_zero_one hφ hφ' _ ha

/-- **The componentwise torsion after cancelling a pair joined by the even-to-odd differential,
in the whole reduced Artinian ring.** Let `φ : D ⟶ C` satisfy the hypotheses of
`HomologicalComplex.parityTorsion_eq_of_cancel_zero_one` over the commutative ring `A`, and let the
entry `a` of the matrix of `C.d 0 1` at the cancelled pair map to a unit of `Q`. Then
`τ(C) = ε · f a · τ(D)` for the componentwise torsions along `f` and some `ε : Q` with
`ε * ε = 1`, so that `ε` is `±1` in each residue field of `Q`. In each residue field where the
complexes are acyclic, `HomologicalComplex.mk_componentwiseParityTorsion_eq_of_cancel_zero_one`
forces this sign to be `(-1) ^ q`; in the other residue fields both torsions vanish and `ε` is
unconstrained there. -/
theorem exists_componentwiseParityTorsion_eq_of_cancel_zero_one
    (ha : IsUnit (f ((c 1).repr ((C.d 0 1).hom (c 0 0)) 0))) :
    ∃ ε : Q, ε * ε = 1 ∧ C.componentwiseParityTorsion c f =
      ε * f ((c 1).repr ((C.d 0 1).hom (c 0 0)) 0) * D.componentwiseParityTorsion e f := by
  simp_rw [mul_assoc]
  exact IsArtinianRing.exists_mul_self_eq_one_and_eq_mul _ fun m ↦
    (mk_componentwiseParityTorsion_eq_of_cancel_zero_one hφ hφ' f m
      (ha.map (Ideal.Quotient.mk m.asIdeal)).ne_zero).trans <| by rw [mul_assoc, map_mul]

end ZeroOne

end Componentwise

end HomologicalComplex
