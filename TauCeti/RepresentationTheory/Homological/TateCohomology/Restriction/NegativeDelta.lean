/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.RepresentationTheory.Homological.GroupHomology.Transfer.Delta
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DeltaGroupHomology
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Restriction.AllDegrees
import TauCeti.RepresentationTheory.Rep.TensorShortExact

/-!
# Restriction commutes with the connecting maps in negative Tate degrees

Let `H` be a subgroup of a finite group `G` and `S` a short exact sequence of
`G`-representations. Restricting `S` to `H` keeps it short exact, and in negative degrees Tate
restriction commutes with the connecting maps of the two long exact sequences:

`\hat{H}^r(G, X₃) ⟶ \hat{H}^{r+1}(G, X₁)`
`       ↓                   ↓`
`\hat{H}^r(H, X₃) ⟶ \hat{H}^{r+1}(H, X₁)`

for `r < 0` (`TauCeti.TateCohomology.δ_comp_res_of_neg`). This is what lets a statement about
restriction be moved across negative degrees by dimension shifting, as in the proof that
restriction is compatible with the Tate cup product.

## Main results

* `TauCeti.TateCohomology.res_comp_toGroupHomology`: in negative degrees, Tate restriction is the
  transfer of group homology through `toGroupHomology`.
* `TauCeti.TateCohomology.δ_comp_res_of_neg`: Tate restriction commutes with the connecting maps in
  negative degrees.

## References

* K. S. Brown, *Cohomology of Groups*, Chapter III, §9 and Chapter VI, §5.
* J. S. Milne, *Class Field Theory*, v4.03, Chapter II, §1.
-/

public noncomputable section

universe u

open CategoryTheory Limits Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

attribute [local instance] Subgroup.fintypeOfFinite Subgroup.fintypeQuotientOfFiniteIndex

/-- **In negative degrees Tate restriction is the transfer of group homology**: through the
comparison `toGroupHomology` of `\hat{H}^{-(n+1)}` with `Hₙ`, restriction to `H` is the transfer. -/
@[reassoc]
theorem res_comp_toGroupHomology (M : Rep R G) (H : Subgroup G) (n : ℕ) :
    res M H (Int.negSucc n) ≫ toGroupHomology (Rep.res H.subtype M) n =
      toGroupHomology M n ≫ TauCeti.groupHomology.transfer M H n := by
  cases n with
  | zero =>
    -- On the class of a norm-zero `z`, both sides are the class of the relative transfer of `z`
    -- in `H₀(H, M)`.
    -- `Int.negSucc 0` is `-1`, where Tate restriction is `HNegOneRes`.
    change res M H (-1) ≫ _ = _
    rw [res_neg_one]
    refine (cancel_epi (HNegOneπ M)).1 ?_
    have h₁ := HNegOneπ_comp_HNegOneRes_assoc M H (toGroupHomology (Rep.res H.subtype M) 0)
    rw [HNegOneπ_comp_toGroupHomology] at h₁
    refine h₁.trans ?_
    rw [HNegOneπ_comp_toGroupHomology_assoc]
    ext z
    simp
  | succ n =>
    rw [res_negSucc_succ, toGroupHomology_eq_negSuccIso_hom, toGroupHomology_eq_negSuccIso_hom,
      negSuccRes_comp_negSuccIso_hom]

/-- Tate restriction commutes with the connecting maps in degrees `-(n+2) ⟶ -(n+1)`. -/
private theorem δ_comp_res_negSucc {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) (n : ℕ) :
    _root_.TateCohomology.δ hS (Int.negSucc (n + 1)) ≫ res S.X₁ H (Int.negSucc n) =
      res S.X₃ H (Int.negSucc (n + 1)) ≫
        _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) (Int.negSucc (n + 1)) := by
  -- Compare in group homology, where restriction is the transfer.
  refine (cancel_mono (toGroupHomology (Rep.res H.subtype S.X₁) n)).1 ?_
  calc _ = toGroupHomology S.X₃ (n + 1) ≫ groupHomology.δ hS (n + 1) n rfl ≫
        TauCeti.groupHomology.transfer S.X₁ H n := by
        rw [Category.assoc, res_comp_toGroupHomology, δ_comp_toGroupHomology_assoc]
    _ = toGroupHomology S.X₃ (n + 1) ≫ TauCeti.groupHomology.transfer S.X₃ H (n + 1) ≫
        groupHomology.δ ((shortExact_res H.subtype).2 hS) (n + 1) n rfl := by
        rw [TauCeti.groupHomology.δ_comp_transfer]
    _ = _ := by
        rw [← res_comp_toGroupHomology_assoc, Category.assoc]
        exact congrArg (_ ≫ ·) (δ_comp_toGroupHomology ((shortExact_res H.subtype).2 hS) n).symm

/-- Tate restriction commutes with the connecting maps in degrees `-1 ⟶ 0`. -/
private theorem δ_comp_res_neg_one {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (H : Subgroup G) :
    _root_.TateCohomology.δ hS (-1) ≫ res S.X₁ H 0 =
      res S.X₃ H (-1) ≫ _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) (-1) := by
  rw [res_zero, res_neg_one]
  refine (cancel_epi (HNegOneπ S.X₃)).1 ?_
  ext z
  -- Lift `z` to `y ∈ X₂`; the norm of `y` is the image of an invariant `x ∈ X₁`.
  obtain ⟨y, hy⟩ := (Rep.epi_iff_surjective S.g).1 hS.epi_g z.1
  have hinj := (Rep.mono_iff_injective S.f).1 hS.mono_f
  obtain ⟨x, hx⟩ := ((Rep.exact_iff_function_exact S).1 hS.exact (S.X₂.ρ.norm y)).1 <| by
    exact (Rep.norm_comm_apply S.g y).symm.trans
      ((congrArg S.X₃.ρ.norm hy).trans (LinearMap.mem_ker.1 z.2))
  have hxG : x ∈ S.X₁.ρ.invariants := fun g ↦ hinj <| by
    rw [Rep.hom_comm_apply, hx, Representation.self_norm_apply]
  -- Over `H`, the relative transfer of `y` lifts that of `z`, with the same norm.
  have hy' : S.g.hom (Representation.relTransfer S.X₂.ρ H y) =
      (Representation.relTransferKerNorm S.X₃.ρ H z : S.X₃) := by
    simp [Representation.relTransfer_apply, Rep.hom_comm_apply, hy]
  have hx' : S.f.hom x = (Rep.res H.subtype S.X₂).ρ.norm (Representation.relTransfer S.X₂.ρ H y) :=
    hx.trans (Representation.norm_relTransfer_apply y).symm
  have hxH : x ∈ (Rep.res H.subtype S.X₁).ρ.invariants := fun h ↦ hxG h
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  rw [δ_HNegOneπ hS z y hy ⟨x, hxG⟩ hx, H0π_comp_H0Res_apply, HNegOneπ_comp_HNegOneRes_apply]
  exact (δ_HNegOneπ ((shortExact_res H.subtype).2 hS) _ _ hy' ⟨x, hxH⟩ hx').symm

/-- **Tate restriction commutes with the connecting maps in negative degrees.** For a short exact
sequence `S` of `G`-representations and a subgroup `H`, restriction to `H` intertwines the
connecting map `\hat{H}^r(G, X₃) ⟶ \hat{H}^{r+1}(G, X₁)` of `S` with the connecting map of its
restriction to `H`, for every `r < 0`. -/
@[reassoc]
theorem δ_comp_res_of_neg {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (H : Subgroup G)
    {r : ℤ} (hr : r < 0) :
    _root_.TateCohomology.δ hS r ≫ res S.X₁ H (r + 1) =
      res S.X₃ H r ≫ _root_.TateCohomology.δ ((shortExact_res H.subtype).2 hS) r := by
  obtain ⟨_ | n, rfl⟩ := Int.eq_negSucc_of_lt_zero hr
  · exact δ_comp_res_neg_one hS H
  · exact δ_comp_res_negSucc hS H n

end TauCeti.TateCohomology
