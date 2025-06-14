import CTree.Euttc
import CTree.LTS

namespace CTree

  theorem euttc_of_lts {t1 t2 : CTree ε ρ} (h : WeakBisim t1 t2) : t1 ≈ t2 := by
    sorry

  theorem lts_of_euttc {t1 t2 : CTree ε ρ} (h : t1 ≈ t2) : WeakBisim t1 t2 := by
    sorry

  theorem euttc_iff_lts {t1 t2 : CTree ε ρ} : t1 ≈ t2 ↔ WeakBisim t1 t2 :=
    ⟨lts_of_euttc, euttc_of_lts⟩

end CTree
