/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.McKay.Basic
public import TauCeti.RepresentationTheory.SU2.Standard

/-!
# The McKay correspondence for finite subgroups of `SU(2)`

Specializing `TauCeti.exists_isMcKayLabelling` to `TauCeti.SU2.stdFDRep H` gives the McKay
correspondence for every nontrivial finite subgroup `H` of `SU(2)`
(`TauCeti.SU2.exists_isMcKayLabelling`), and `TauCeti.SU2.stdFDRepConjIso` transports McKay
labellings between conjugate subgroups (`TauCeti.SU2.isMcKayLabelling_conj_iff` and
`TauCeti.SU2.isMcKayLabelling_conj`).
-/

public section

open CategoryTheory

namespace TauCeti.SU2

/-- **The McKay correspondence for finite nontrivial subgroups of `SU(2)`.** -/
theorem exists_isMcKayLabelling (H : Subgroup SU2) [Finite H] [Nontrivial H] :
    ∃ (t : AffineDynkinType) (e : SimpleClasses (FDRep ℂ H) ≃ Fin t.nodes),
      t.Valid ∧ IsMcKayLabelling (stdFDRep H) t e :=
  TauCeti.exists_isMcKayLabelling (stdFDRep H) (finrank_stdFDRep H) (ρ_stdFDRep_injective H)
    (det_ρ_stdFDRep H)

/-- Conjugation by `g : SU2` preserves McKay labellings of the standard representation between
conjugate subgroups `H` and `K = H.map (MulAut.conj g : SU2 →* SU2)`. -/
theorem isMcKayLabelling_conj_iff {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (t : AffineDynkinType)
    (e : SimpleClasses (FDRep ℂ K) ≃ Fin t.nodes) :
    IsMcKayLabelling (stdFDRep H) t
        ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ)
            (((MulAut.conj g).subgroupMap H).trans
              (MulEquiv.subgroupCongr hK.symm)))).symm.trans e) ↔
      IsMcKayLabelling (stdFDRep K) t e := by
  rw [← isMcKayLabelling_congr (stdFDRepConjIso hK) t, isMcKayLabelling_res_iff]

/-- Transport a McKay labelling of `TauCeti.SU2.stdFDRep K` to a conjugate subgroup `H` with
`K = H.map (MulAut.conj g : SU2 →* SU2)`. -/
theorem isMcKayLabelling_conj {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) {t : AffineDynkinType}
    {e : SimpleClasses (FDRep ℂ K) ≃ Fin t.nodes} (h : IsMcKayLabelling (stdFDRep K) t e) :
    IsMcKayLabelling (stdFDRep H) t
      ((SimpleClasses.equiv (Action.resEquiv (FGModuleCat ℂ)
          (((MulAut.conj g).subgroupMap H).trans
            (MulEquiv.subgroupCongr hK.symm)))).symm.trans e) :=
  h.of_mulEquiv _ (stdFDRepConjIso hK)

end TauCeti.SU2
