/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.DistinguishedSquare
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Diagonal

/-!
# Nisnevich sheaves on elementary distinguished squares

Every sheaf of sets `F` for the Nisnevich topology sends an elementary distinguished square
`U ×_X V → U, V → X` to a pullback square: the map `F(X) → F(U) ×_{F(U ×_X V)} F(V)` is bijective
(Morel–Voevodsky, §3.1, the only-if direction of Proposition 1.4). This is the sheaf condition for
the Nisnevich covering `{j, p}`, and needs no sheafification.

The only point beyond the definition of a sheaf is the compatibility of a section `b ∈ F(V)` with
itself on `V ×_X V`. The scheme `V ×_X V` is covered by the diagonal `V ⟶ V ×_X V`, an open
immersion because `p` is étale, and by its open part over `U`
(`TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isNisnevichCovering_diagonal`):
over the reduced closed complement `Z` of `U`, the base change of `p` is an isomorphism, so
`V ×_X V` restricted to `Z` lies in the diagonal. The two pullbacks of `b` agree on the diagonal
trivially, and on the part over `U` both are the pullback of the section `a ∈ F(U)` that agrees
with `b` on `U ×_X V`.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isNisnevichCovering_diagonal`:
  the diagonal of `p` and the base change of `j` to `V ×_X V` form a Nisnevich covering.
* `TauCeti.AlgebraicGeometry.Scheme.ElementaryDistinguishedSquare.isPullback_of_isSheaf`:
  a Nisnevich sheaf of sets sends an elementary distinguished square to a pullback square.

## References

* F. Morel and V. Voevodsky, *𝔸¹-homotopy theory of schemes*, Publ. Math. IHÉS 90 (1999),
  §3.1, Proposition 1.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

universe v u

namespace TauCeti.AlgebraicGeometry.Scheme

namespace ElementaryDistinguishedSquare

variable {X : AlgebraicGeometry.Scheme.{u}} (Q : ElementaryDistinguishedSquare X)

/-- The two morphisms covering `V ×_X V`, indexed by `Bool`: the diagonal of `p`
(`true`) and the base change of `j` along `V ×_X V ⟶ X` (`false`). -/
noncomputable abbrev diagonalArrows : ∀ b : Bool,
    (Bool.rec (Limits.pullback (Limits.pullback.fst Q.p Q.p ≫ Q.p) Q.j) Q.V b :
      AlgebraicGeometry.Scheme.{u}) ⟶ Limits.pullback Q.p Q.p :=
  Bool.rec (motive := fun b ↦ (Bool.rec (Limits.pullback (Limits.pullback.fst Q.p Q.p ≫ Q.p) Q.j)
      Q.V b : AlgebraicGeometry.Scheme.{u}) ⟶ Limits.pullback Q.p Q.p)
    (Limits.pullback.fst _ _) (Limits.pullback.diagonal Q.p)

/-- **The diagonal of `p` and the part of `V ×_X V` over `U` cover `V ×_X V`**: both are open
immersions, and every point of `V ×_X V` over the reduced closed complement of `U` lies in the
diagonal, since the base change of `p` to that complement is an isomorphism. -/
theorem isNisnevichCovering_diagonal : IsNisnevichCovering Q.diagonalArrows := by
  apply isNisnevichCovering_of_zariski
  rw [AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun w ↦ ?_, fun b ↦ by cases b <;> dsimp <;> infer_instance⟩
  set I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal Q.j.opensRange.compl
  by_cases hw : (Limits.pullback.fst Q.p Q.p ≫ Q.p) w ∈ Set.range Q.j
  · obtain ⟨u, hu⟩ := hw
    obtain ⟨w', hw', -⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback w u hu.symm
    exact ⟨false, w', hw'⟩
  · refine ⟨true, ?_⟩
    have hz : (Limits.pullback.fst Q.p Q.p ≫ Q.p) w ∈ Set.range I.subschemeι := by
      rw [AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι,
        AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
      simpa using hw
    obtain ⟨z, hz⟩ := hz
    obtain ⟨w', hw', -⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback w z hz.symm
    have hd := Limits.pullback.fst_eq_comp_diagonal_of_isIso_snd Q.p I.subschemeι
    refine ⟨(Limits.pullback.fst (Limits.pullback.fst Q.p Q.p ≫ Q.p) I.subschemeι ≫
      Limits.pullback.fst Q.p Q.p) w', ?_⟩
    rw [← hw']
    conv_rhs => rw [hd]
    exact (AlgebraicGeometry.Scheme.Hom.comp_apply _ _ _).symm

variable {F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v} (hF : Presieve.IsSheaf nisnevichTopology F)
include hF

/-- A Nisnevich sheaf is separated for the covering `{j, p}`: sections over `X` agreeing on `U` and
on `V` are equal. -/
theorem ext_of_isSheaf {s t : F.obj (op X)} (hj : F.map Q.j.op s = F.map Q.j.op t)
    (hp : F.map Q.p.op s = F.map Q.p.op t) : s = t := by
  refine ((Presieve.isSheafFor_iff_generate _).2
    (hF _ Q.ofArrows_mem_nisnevichTopology)).isSeparatedFor.ext ?_
  rintro _ _ ⟨b⟩
  cases b
  · exact hp
  · exact hj

/-- A section `b` of a Nisnevich sheaf over `V` that agrees on `U ×_X V` with a section over `U`
has equal pullbacks along the two projections `V ×_X V ⟶ V`. -/
theorem map_fst_eq_map_snd_of_isSheaf {a : F.obj (op Q.U)} {b : F.obj (op Q.V)}
    (hab : F.map (Limits.pullback.fst Q.j Q.p).op a = F.map (Limits.pullback.snd Q.j Q.p).op b) :
    F.map (Limits.pullback.fst Q.p Q.p).op b = F.map (Limits.pullback.snd Q.p Q.p).op b := by
  have hS : Sieve.ofArrows _ Q.diagonalArrows ∈ nisnevichTopology (Limits.pullback Q.p Q.p) :=
    Precoverage.generate_mem_toGrothendieck
      (ofArrows_mem_nisnevichPrecoverage_iff.2 Q.isNisnevichCovering_diagonal)
  refine ((Presieve.isSheafFor_iff_generate _).2 (hF _ hS)).isSeparatedFor.ext ?_
  rintro _ _ ⟨c⟩
  cases c
  · -- Over `U`, both pullbacks of `b` are pullbacks of `a`.
    set k := Limits.pullback.fst (Limits.pullback.fst Q.p Q.p ≫ Q.p) Q.j
    set l := Limits.pullback.snd (Limits.pullback.fst Q.p Q.p ≫ Q.p) Q.j
    -- Each projection `π` restricted along `k` factors through `U ×_X V`, with first factor `l`.
    have e : ∀ π : Limits.pullback Q.p Q.p ⟶ Q.V,
        π ≫ Q.p = Limits.pullback.fst Q.p Q.p ≫ Q.p → F.map (k ≫ π).op b = F.map l.op a := by
      intro π hπ
      have hk : k ≫ π = Limits.pullback.lift l (k ≫ π)
          (by rw [Category.assoc, hπ]; exact Limits.pullback.condition.symm) ≫
            Limits.pullback.snd Q.j Q.p := by
        simp
      rw [hk, op_comp, Functor.map_comp_apply, ← hab, ← Functor.map_comp_apply, ← op_comp,
        Limits.pullback.lift_fst]
    dsimp
    simp only [← Functor.map_comp_apply, ← op_comp]
    rw [e _ rfl, e _ Limits.pullback.condition.symm]
  · -- On the diagonal, both projections are the identity.
    dsimp
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      Limits.pullback.diagonal_fst, Limits.pullback.diagonal_snd]

/-- **Nisnevich sheaves on elementary distinguished squares** (Morel–Voevodsky, §3.1, the
only-if direction of Proposition 1.4): a sheaf of sets `F` for the Nisnevich topology sends an
elementary distinguished square to a pullback square, so
`F(X) → F(U) ×_{F(U ×_X V)} F(V)` is bijective. -/
theorem isPullback_of_isSheaf :
    IsPullback (F.map Q.j.op) (F.map Q.p.op) (F.map (Limits.pullback.fst Q.j Q.p).op)
      (F.map (Limits.pullback.snd Q.j Q.p).op) := by
  rw [Types.isPullback_iff]
  refine ⟨?_, fun s t ⟨hj, hp⟩ ↦ Q.ext_of_isSheaf hF hj hp, fun a b hab ↦ ?_⟩
  · rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, Limits.pullback.condition]
  · -- Glue `a` and `b` along the covering `{j, p}`.
    have hsheaf : (Presieve.ofArrows _ Q.arrows).IsSheafFor F :=
      (Presieve.isSheafFor_iff_generate _).2 (hF _ Q.ofArrows_mem_nisnevichTopology)
    rw [Presieve.isSheafFor_arrows_iff_pullbacks] at hsheaf
    obtain ⟨t, ht, -⟩ := hsheaf (fun c ↦ Bool.rec b a c) (by
      intro c d
      cases c <;> cases d
      · exact Q.map_fst_eq_map_snd_of_isSheaf hF hab
      · -- `Q.arrows` and the family `Bool.rec b a` evaluate by `Bool.rec` reduction.
        change F.map (Limits.pullback.fst Q.p Q.j).op b = F.map (Limits.pullback.snd Q.p Q.j).op a
        have h₁ : Limits.pullback.fst Q.p Q.j =
            (Limits.pullbackSymmetry Q.p Q.j).hom ≫ Limits.pullback.snd Q.j Q.p := by simp
        have h₂ : Limits.pullback.snd Q.p Q.j =
            (Limits.pullbackSymmetry Q.p Q.j).hom ≫ Limits.pullback.fst Q.j Q.p := by simp
        rw [h₁, h₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hab]
      · exact hab
      · -- As above, by `Bool.rec` reduction.
        change F.map (Limits.pullback.fst Q.j Q.j).op a = F.map (Limits.pullback.snd Q.j Q.j).op a
        rw [Limits.fst_eq_snd_of_mono_eq])
    exact ⟨t, ht true, ht false⟩

end ElementaryDistinguishedSquare

end TauCeti.AlgebraicGeometry.Scheme
